#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define WSIZE   4                                 //워드 크기 
#define DSIZE   8                                 //더블 워드 크기
#define CHUNKSIZE (1<<12)                         //힙의 끝을 현재보다 더 뒤로 밀어서 새로운 가용(free space)공간 확보
//2의 12승 = 4096(4kb)

#define MAX(x, y) ((x) > (y) ? (x) : (y))         //x, y를 받아서 더 큰 값을 반환
#define PACK(size, alloc, prev_alloc) ((size) | (alloc) | ((prev_alloc) << 1)) //size와 alloc을 받아 or 연산을 한다. ++ 

                                                //size는 항상 8의 배수로 정렬되기 때문에 하위 3비트는 0, 맨 마지막 1비트를 할당 여부 표시
#define GET(p) (*(unsigned int *)(p))             //p를 받아와서 unsigned int의 포인터로 형변환, 포인터의 값을 역참조
#define PUT(p, val) (*(unsigned int *)(p) = (val)) //p가 가리키는 워드에 val을 저장한다.

#define GET_SIZE(p) (GET(p) & ~0x7)               //하위 3비트를 삭제하는 연산, 총 size를 반환한다.
#define GET_ALLOC(p) (GET(p) & 0x1)               //마지막 비트의 값을 구하는 연산
#define GET_PREV_ALLOC(p) ((GET(p) & 0x2) >> 1)

#define HDRP(bp)    ((char *)(bp) - WSIZE)         //bp는 Payload의 시작 위치를 가리킨다. 때문에 bp보다 4바이트 앞에 헤더가 있다.
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //풋터의 시작을 가리키는 포인터 반환, 반환된 포인터는 char형 포인터  

#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((void *)(bp) - WSIZE)))   //다음 블록의 블록 포인터를 반환
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((void *)(char *)(bp) - DSIZE)))   //이전 블록의 블록 포인터를 반환


#define GET_ADDRESS(p) (*(unsigned long *)(p))              //포인터의 주소를 읽는 연산
#define GET_PREV(bp)  (GET_ADDRESS(bp))                     //bp의 prev bp를 찾는 메크로
#define GET_NEXT(bp) (GET_ADDRESS((char *)(bp)+DSIZE))      //bp의 next bp를 찾는 메크로
#define PUT_ADDRESS(p, address) (*(unsigned long *)(p) = (unsigned long)(address)) //주소값을 p가 가리키는 워드에 저장
#define SET_PREV(bp, prev_ptr) (PUT_ADDRESS(bp, prev_ptr))                     //bp의 prev에 prev_ptr을 저장
#define SET_NEXT(bp, next_ptr) (PUT_ADDRESS(((char *)(bp) + DSIZE), next_ptr)) //bp의 next에 next_ptr을 저장

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

#define ALIGNMENT 8                                     //기본 8바이트 정렬 유지
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) //8바이트 정렬을 시키는 함수
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


static char *heap_listp;               //char형 포인터 heap_listp를 선언 
// void *next_bp = NULL; //void형 포인터 next_fit 선언
static void *first_free_bp = NULL;     //명시적 가용 리스트의 Root


static void free_list_link(void *bp) //가용블록을 기준으로 탐색해야 한다.
{   //가용 블록을 받아서 bp를 기준으로 앞뒤 블록을 이어주는 함수
    //bp의 prev, next는 사라진다.
    void *prev = GET_PREV(bp);      //bp의 이전 블록을 prev로 지정
    void *next = GET_NEXT(bp);      //bp의 다음 블록을 next로 지정

    if(prev && next)
    {//현재 블록 prev랑 next가 모두 존재할 때
        SET_NEXT(prev, next);       //이전 블록의 next를 다음블록으로 지정
        SET_PREV(next, prev);       //다음 블록의 prev를 이전블록으로 지정
    }
    else if(!prev && next)  //bp가 루트인 경우
    {
        SET_PREV(next, NULL);       //다음 블록의 이전을 NULL로 지정
        first_free_bp = next;//다음 블록을 루트로 설정
    }
    else if(prev && !next)   //bp 맨 뒤의 블록인 경우
    {
        SET_NEXT(prev, NULL);       //이전 블록의 다음 블록을 NULL로 지정
    }
    else                            //양쪽이 다 NULL인 경우, bp가 한 개의 가용 리스트 인경우
    {
        first_free_bp = NULL;       //명시적 가용 리스트의 Root를 NULL으로 지정
    }
    // 모든 조건 검사, 링크가 끝나고
    SET_PREV(bp, NULL);             //bp의 prev를 NULL로 한다.
    SET_NEXT(bp, NULL);             //bp의 next를 NULL로 한다.
    //과정이 끝나면 bp를 기준으로 앞뒤가 연결되고 bp는 아무런 next, prev를 가지지 않는다.
}
//free list의 맨 앞에 bp를 넣는 함수
static void insert_first(void *bp)  
{
    SET_PREV(bp,NULL);              //bp의 이전 블록을 NULL으로 지정
    SET_NEXT(bp,NULL);              //bp의 다음 블록을 NULL으로 지정

    //현재 first_free_bp이 있다면 새 블록을 앞에 붙인다.
    if(first_free_bp != NULL)
    {
        SET_PREV(first_free_bp, bp);//현재 Root의 이전 블록을 bp로 지정
    }
    
    SET_NEXT(bp, first_free_bp);    //bp의 next를 현재 Root로 지정
    SET_PREV(bp, NULL);             //bp의 prev를 NULL로 지정

    first_free_bp = bp;             //bp를 현재 가용 블록의 Root로 설정한다.
}

//경계 태그 연결을 사용해서 인접 가용 블록들과 통합한다.
static void *coalesce(void *bp)        
{
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));       //이전 블록의 alloc 값(할당 여부)를 prev_alloc에 대입한다.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록의 alloc 값(할당 여부)를 next_alloc에 대입한다
    size_t size = GET_SIZE(HDRP(bp));                   //size는 현재 블록의 사이즈

    if (prev_alloc && next_alloc){}                     //양쪽이 다 할당당 블록일 때 아무 동작을 하지 않는다.

    else if(prev_alloc && !next_alloc)                  //next_alloc이 가용 블록이라면
    {//bp의 next 블록이 사라지고 병합을 하기 때문에
        free_list_link(NEXT_BLKP(bp));                  //bp의 next를 기준으로 prev와 next를 이어준다.

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));          //size(현재 블록의 사이즈)에 다음 블록의 size를 더한다.
        PUT(HDRP(bp), PACK(size, 0, prev_alloc));       //PACK(size와 0을 받아서 or연산을 한다.) 해당 값을 현재 bp의 헤더가 가리키는 워드에 저장한다. 
        PUT(FTRP(bp), PACK(size, 0, prev_alloc));       //PACK한 값을 현재 bp의 풋터(FTRP 메크로에서 확장된 블록 사이즈로 풋터를 구한다.) 해당 값을 확장된 bp의 풋터가 가리키는 워드에 저장
    }

    else if(!prev_alloc && next_alloc)                  //prev_alloc이 할당되지 않았다면
    {//bp의 prev 블록이 사라지고 병합을 하기 때문에
        free_list_link(PREV_BLKP(bp));                  //bp의 prev를 기준으로 prev와 next를 이어준다.

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));          //size(현재 블록의 사이즈에)에 이전 블록의 size를 더한다.
        PUT(FTRP(bp), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));                 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));       
        bp = PREV_BLKP(bp);                             //현재 bp를 이전 블록의 bp로 변경한다.
    }

    else
    {//bp의 양쪽 다 가용 블록일 경우
        //방향이 상관 있을줄 알았는데 큰 상관 없었음
        free_list_link(NEXT_BLKP(bp));                 //bp의 next를 기준으로 prev와 next를 이어준다.        
        free_list_link(PREV_BLKP(bp));                 //bp의 prev를 기준으로 prev와 next를 이어준다.

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +         //size(현재 블록의 사이즈)에 이전 블록과 다음 블록의 size를 더한다. 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));        //PACK한 값을 이전 블록의 헤더가 가리키는 워드에 저장한다.
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));        //PACK한 값을 다음 블록의 풋터가 가리키는 워드에 저장한다.(next 블록 끝이 합쳐진 블록 끝이 되기 때문)
        bp = PREV_BLKP(bp);                           //현재 bp를 이전 블록의 bp로 변경한다.
    }

    // 다음 블록의 prev_alloc 수정
    if(!GET_ALLOC(HDRP(bp)))                    //현재 블록이 할당되지 않았다면
    {
        void *next_bp = NEXT_BLKP(bp);          //bp의 다음 블록을 next_bp로 지정
        if (GET_SIZE(HDRP(next_bp)) != 0) {     // 에필로그 아니면
            size_t next_header = GET(HDRP(next_bp));  //next_header에 다음 블록의 포인터 값을 대입
            PUT(HDRP(next_bp), (next_header & ~0x2)); // 다음 블록의 prev_alloc을 0으로 만든다.
        }
        else { // 에필로그면
            PUT(HDRP(next_bp), PACK(0, 1, 0));       //이전 블록을 가용 상태로 만든다.
        }
    }
    insert_first(bp);                               //병합이 끝난 블록을 free list의 first로 만든다.
    // next_bp = bp;
    return bp;                                          //현재의 bp값을 반환한다.
}

//extend_heap 함수는 힙이 초기화 될 때와 mm_malloc이 적당한 맞춤 fit을 찾지 못했을 때 호출된다.
static void *extend_heap(size_t words) // 매개변수로 words를 받아 void형 포인터를 반환한다. 
{
    char *bp;                           //블록을 가리키는 포인터 bp를 선언
    size_t size;                       //size_t는 부호 없는 정수 타입(unsigned int 또는 unsigned long)이다. 
    size_t prev_alloc;

    size = ALIGN(words * WSIZE);        //size를 4 * 할당블록의 사이즈 * 8바이트의 값

    if((long)(bp = mem_sbrk(size)) == -1)                              //size만큼 힙을 할당하고 할당에 성공하면 확장 전(힙의 끝을 가리키는)힙의 포인터(void* 타입)를 반환한다.                    
        return NULL;                                                

    prev_alloc = GET_PREV_ALLOC(HDRP(bp));                //이전 블록의 할당 여부를 확인한다. (에필로그의 헤더 포인터로 이동)
    PUT(HDRP(bp), PACK(size, 0, prev_alloc));             //PACK(size와 alloc을 받아 둘을 합친다.) 여기서는 alloc을 0으로 한다. HDRP 메크로를 사용해 bp의 헤더를 찾는다. 헤더에 PACK 한 값을 대입한다.
    PUT(FTRP(bp), PACK(size, 0, prev_alloc));             //PACK(size와 alloc을 받아 둘을 합친다.) 여기서는 alloc을 0으로 한다. FTRP 메크로를 사용해 bp의 풋터를 찾는다. 풋터에 PACK 한 값을 대입한다
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1, 0));              //PACK(여기서 alloc을 1으로 설정한 값) 다음의 bp를 찾는다. 다음 bp의 헤더를 alloc 1로 설정한다. 새 에필로그 블록의 헤더가 된다.
    
    bp = coalesce(bp);                                    //bp를 병합한다.

    // next_bp = bp;
    return bp;                                            //coalesce(bp)을 호출한다. coalesce 함수는 두 개의 가용블록을 통합하고 통합된 블록 포인터를 리턴한다. 앞 부분을 확인해서 합친다.
}
//heap 초기화 함수
int mm_init(void)                                         
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) //힙을 16바이트 확장
        return -1;

    PUT(heap_listp, 0);                                     //현재 위치, 힙의 시작에 0을 넣는다. 16바이트 정렬을 위해서           
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1, 1));         //프롤로그의 헤더 할당을 표시
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1, 1));         //프롤로그의 풋터
    PUT(heap_listp + (3*WSIZE), PACK(0, 1, 1));             //에필로그의 헤더

    heap_listp += (2*WSIZE);                    //힙의 payload의 시작 부분을 가리킨다.(프롤로그 풋터의 뒤)
    first_free_bp = NULL;                       // 가용 리스트 초기화(중요!)

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)                  //extend_heap함수는 힙할당에 실패하면 NULL을 반환한다.
        return -1;                                             //확장에 실패 했을 때 -1을 반환한다.
    return 0;                                                  //정상적인 동작이 끝나면 0을 반환한다.
}


static void *best_fit(size_t asize)                         //best-fit 방식으로 가용블록을 탐색한다.
{
    void *bp;            //void형 포인터 bp를 선언
    void *best_p = NULL;//best_fit의 값을 저장할 포인터

    for (bp = first_free_bp; bp != NULL; bp = GET_NEXT(bp))   //heap의 시작 주소로부터 에필로그 헤더까지 반복한다. bp을 다음 bp로 변환하면서 이동
    {
        size_t current_size = GET_SIZE(HDRP(bp));

        if(asize <= current_size)       //현재 bp가 할당되지 않았고 요청한 사이즈보다 크거나 같으면
        {
            if(asize == current_size)                      //현재 bp가 요청 사이즈와 같다면 바로 반환
            {
                return bp;
            }
            if(best_p == NULL || current_size < GET_SIZE(HDRP(best_p))) //best_p가 NULL이거나 현재 bp의 사이즈가 best_p의 사이즈 보다 작을때
            {
                best_p = bp;                                 
            }                      
        }
    }
    if(best_p == NULL)
    {
        return NULL;                 //모든 탐색이 끝나고 해당 크기가 없다면 NULL을 반환
    }
    return best_p;                   //best_p를 반환
}

//할당 할 블록의 나머지 부분이 최소 블록 크기보다 크거나 같을 경우 분할하는 함수
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));     //csize는 bp의 size   
    free_list_link(bp);                    //bp를 기준으로 prev, next 가용블록을 이어준다.(bp는 할당되기 때문)

    if ((csize - asize) >= (32))      //bp의 사이즈에서 asize를 뺀 값이 32비트보다 크다면
    { 
        PUT(HDRP(bp), PACK(asize, 1, GET_PREV_ALLOC(HDRP(bp))));//asize만큼 할당 블록으로 만든다.

        void *free_bp = NEXT_BLKP(bp);               //bp의 다음 블록(새롭게 분할된 블록)
        PUT(HDRP(free_bp), PACK(csize-asize, 0, 1)); //헤더와 풋터에 size 할당 여부를 넣는다.
        PUT(FTRP(free_bp), PACK(csize-asize, 0, 1));

        insert_first(free_bp);                       //가용 블록의 가장 앞으로 삽입한다.
    } 
    else //더 작다면 전체를 할당한다.
    {                                
        PUT(HDRP(bp), PACK(csize, 1, GET_PREV_ALLOC(HDRP(bp)))); //이전 블록의 할당여부와 가용블록의 전체 사이즈로 할당한다.
    }
    // 다음 블록 prev_alloc 업데이트
    void *next_bp = NEXT_BLKP(bp);                          //bp의 다음 블록을 next_bp로 선언
    if (GET_SIZE(HDRP(next_bp)) != 0)                       //에필로그 블록이 아니라면
    {
        size_t nh = GET(HDRP(next_bp));                     //다음 블록의 값을 참조한다.
        PUT(HDRP(next_bp), nh | 0x2);                       //다음 블록의 prev_alloc을 1로 만든다.
    } 
    else                                                    //에필로그 블록이라면
    {
        PUT(HDRP(next_bp), PACK(0,1,1));                    //에필로그 블록에 prev_alloc을 1로 만든다.
    }
}

//요청한 size의 메모리를 할당하고 해당 메모리의 시작을 가리키는 포인터를 반환하는 함수
void *mm_malloc(size_t size)                                
{
    size_t asize;           //asize선언 (할당 요청을 위한 정렬된 블록 크기)
    size_t extendsize;      //extendsize 선언 (힙 확장을 위한 크기)
    char *bp;               //bp 포인터 선언 (블록 포인터)

    if(size == 0)           //size가 0이면
        return NULL;        //NULL을 반환
    
    if(size <= 24)       //size가 24바이트 이하이면(프롤로그 헤더 + 풋터 + 에필로그 헤더 = 8)
        asize = 32;      //최소 블록 크기(32바이트)로 설정
    //결국 중요한 부분은 최소 블록의 크기(최소 블록의 크기가 16바이트를 보장해야 함)
    else                    
        asize = ALIGN(size + DSIZE);    //요청 크기에 오버헤드(헤더 + 풋터) 추가 후, 8바이트 단위로 올림 정렬하여 asize 계산
    
    //요청 크기 이상인 가용 블록 찾기
    if((bp = best_fit(asize)) != NULL)              //bp에 best_fit을 한 값을 대입, 해당 값이 NULL이 아닐때
    {   
        place(bp, asize);                           //남는 공간이 최소 블록 크기 이상이면 분할
        return bp;                                  //bp를 반환
    }
    //할당 할수 있는 가용 블록이 없는경우
    extendsize = MAX(asize, CHUNKSIZE);                 //현재 요청한 사이즈(바이트 단위)와, CHUNKSIZE를 비교해서 더 큰 값을 대입 
    if((bp = extend_heap(extendsize / WSIZE)) == NULL)  //bp에 extendsize를 확장하고 확장 전 힙의 시작 위치를 가리키는 포인터를 대입 
        return NULL;                                    //NULL을 반환

    place(bp, asize);                                   //남는 공간이 최소 블록 크기 이상이면 분할
    return bp;                                          //bp를 반환
}

// 블록을 가용 상태로 표시하고, 인접 가용 블록들과 통합하는 함수
void mm_free(void *bp)                   
{
    size_t size = GET_SIZE(HDRP(bp));          //bp의 블록크기

    PUT(HDRP(bp), PACK(size, 0, GET_PREV_ALLOC(HDRP(bp))));  // 블록 헤더에 (크기, 미할당 상태 0)을 기록
    PUT(FTRP(bp), PACK(size, 0, GET_PREV_ALLOC(HDRP(bp))));  // 블록 풋터에도 기록

    // 다음 블록 prev_alloc 업데이트
    void *next_bp = NEXT_BLKP(bp);
    if (GET_SIZE(HDRP(next_bp)) != 0) 
    {
        size_t next_header = GET(HDRP(next_bp));
        PUT(HDRP(next_bp), (next_header & ~0x2)); // prev_alloc = 0으로 만든다
    } 
    else 
    {
        PUT(HDRP(next_bp), PACK(0, 1, 0)); // 에필로그
    }
    bp = coalesce(bp);                               //경계 태그 연결을 사용해서 인접 가용 블록들과 통합
}       

// 할당한 메모리의 사이즈를 변경하는 함수
void *mm_realloc(void *ptr, size_t size)        //ptr과 새로 요청하는 전체 size를 매개변수로 받는다.
{
    if(ptr == NULL)                             //ptr이 NULL이면
        return mm_malloc(size);                 //malloc한 값의 포인터를 반환한다.

    if(size == 0)                               //size가 0이면 
    {
        mm_free(ptr);                           //ptr을 할당 해제한다.
        return NULL;
    }
    
    size_t oldsize = GET_SIZE(HDRP(ptr));       //기존 블록 크기
    size_t newsize = ALIGN(size + DSIZE);       //새로 요청한 크기 + 오버헤드

    if(newsize <= oldsize)                      //기존 블록 이하면 그냥 반환
    {
        return ptr;
    }

    else
    {
        void *next_bp = NEXT_BLKP(ptr);         //다음 블록 포인터
        if(!GET_ALLOC(HDRP(next_bp)) && !GET_PREV_ALLOC(HDRP(ptr)))
        {
            void *prev_bp = PREV_BLKP(ptr);      //이전 블록 포인터
            void *next_bp = NEXT_BLKP(ptr);         //다음 블록 포인터
            size_t prev_size = GET_SIZE(HDRP(prev_bp));
            size_t next_size = GET_SIZE(HDRP(next_bp));

            if(oldsize + prev_size + next_size >= newsize)
            {
                free_list_link(prev_bp);
                free_list_link(next_bp);

                void *next_next_bp = NEXT_BLKP(next_bp);  //next_bp 다음 블록의 포인터
                size_t payload_size = oldsize - DSIZE; //payload의 size
                memmove(prev_bp, ptr, payload_size);    //prev_bp에 ptr부터 payload_size 만큼 이동한다.
                
                if(GET_SIZE(HDRP(next_next_bp)) != 0) //에필로그가 아니라면 
                {
                    PUT(HDRP(next_next_bp), (GET(HDRP(next_next_bp))) | 0x2);                    
                }
                else
                {
                    PUT(HDRP(next_next_bp), PACK(0, 1, 1));
                }

                PUT(HDRP(prev_bp), PACK(oldsize + prev_size + next_size, 1, GET_PREV_ALLOC(HDRP(prev_bp))));
                
                return prev_bp;
            }
        }
        else if(!GET_ALLOC(HDRP(next_bp)))           //다음 블록이 가용 블록이면
        {

            size_t next_size = GET_SIZE(HDRP(next_bp));
            if(oldsize + next_size >= newsize)
            {
                void *next_next_bp = NEXT_BLKP(next_bp);  //next_bp 다음 블록의 포인터
                if(GET_SIZE(HDRP(next_next_bp)) != 0) //에필로그가 아니라면 
                {
                    PUT(HDRP(next_next_bp), (GET(HDRP(next_next_bp))) | 0x2);                    
                }
                else
                {
                    PUT(HDRP(next_next_bp), PACK(0, 1, 1));
                }
                free_list_link(next_bp);
                PUT(HDRP(ptr), PACK(oldsize + next_size, 1, GET_PREV_ALLOC(HDRP(ptr))));
                // PUT(FTRP(ptr), PACK(oldsize + next_size, 1, GET_PREV_ALLOC(HDRP(ptr))));

                return ptr; 
            }
        }
        else if(!GET_PREV_ALLOC(HDRP(ptr)))
        {
            void *prev_bp = PREV_BLKP(ptr);      //이전 블록 포인터
            size_t prev_size = GET_SIZE(HDRP(prev_bp));
            
            if(oldsize + prev_size >= newsize)
            {
                void *next_bp = NEXT_BLKP(ptr);
                free_list_link(prev_bp);

                size_t payload_size = oldsize - DSIZE; //payload의 size
                memmove(prev_bp, ptr, payload_size);    //prev_bp에 ptr부터 payload_size 만큼 이동한다.

                PUT(HDRP(prev_bp), PACK(oldsize + prev_size, 1, GET_PREV_ALLOC(HDRP(prev_bp))));

                return prev_bp;
            }
        }

        // 그렇지 않다면 malloc후 복사
        void *newptr = mm_malloc(size);
        if(newptr == NULL)
        {
            return NULL;
        }

        size_t copysize = oldsize - DSIZE;
        if (size < copysize)
            copysize = size;

        memmove(newptr, ptr, copysize);
        mm_free(ptr);
        return newptr;            
    }
}
