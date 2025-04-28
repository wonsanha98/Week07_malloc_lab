/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
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

#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))   //다음 블록의 블록 포인터를 반환
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))   //이전 블록의 블록 포인터를 반환

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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 * mm_init - initialize the malloc package.
 */

static char *heap_listp;               //char형 포인터 heap_listp를 선언 
void *next_bp = NULL; //void형 포인터 next_fit 선언


//경계 태그 연결을 사용해서 인접 가용 블록들과 통합한다.
static void *coalesce(void *bp)        
{
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));       //이전 블록의 alloc 값(할당 여부)를 prev_alloc에 대입한다.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록의 alloc 값(할당 여부)를 next_alloc에 대입한다
    size_t size = GET_SIZE(HDRP(bp));                   //size는 현재 블록의 사이즈

    if (prev_alloc && next_alloc)                       //prev_alloc 과 next_alloc이 1이라면
    {
        return bp;                                      //현재의 bp를 반환한다.
    }

    else if(prev_alloc && !next_alloc)                  //next_alloc이 할당되지 않았다면
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));          //size(현재 블록의 사이즈)에 다음 블록의 size를 더한다.
        PUT(HDRP(bp), PACK(size, 0, prev_alloc));                   //PACK(size와 0을 받아서 or연산을 한다.) 해당 값을 현재 bp의 헤더가 가리키는 워드에 저장한다. 
        PUT(FTRP(bp), PACK(size, 0, prev_alloc));                   //PACK한 값을 현재 bp의 풋터(FTRP 메크로에서 확장된 블록 사이즈로 풋터를 구한다.) 해당 값을 확장된 bp의 풋터가 가리키는 워드에 저장
    }

    else if(!prev_alloc && next_alloc)                  //prev_alloc이 할당되지 않았다면
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));          //size(현재 블록의 사이즈에)에 이전 블록의 size를 더한다.
        PUT(FTRP(bp), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));                 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));       
        bp = PREV_BLKP(bp);                             //현재 bp를 이전 블록의 bp로 변경한다.
    }

    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +         //size(현재 블록의 사이즈)에 이전 블록과 다음 블록의 size를 더한다. 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));        //PACK한 값을 이전 블록의 헤더가 가리키는 워드에 저장한다.
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0, GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));        //PACK한 값을 다음 블록의 풋터가 가리키는 워드에 저장한다.(next 블록 끝이 합쳐진 블록 끝이 되기 때문)
        bp = PREV_BLKP(bp);                             //현재 bp를 이전 블록의 bp로 변경한다.
    }
        // 다음 블록의 prev_alloc 수정
    if(!GET_ALLOC(HDRP(bp)))
    {
        void *next_bp = NEXT_BLKP(bp);
        if (GET_SIZE(HDRP(next_bp)) != 0) { // 에필로그 아니면
            size_t next_header = GET(HDRP(next_bp));
            PUT(HDRP(next_bp), (next_header & ~0x2)); // prev_alloc을 0으로 만든다
        }
        else { // 에필로그면
            PUT(HDRP(next_bp), PACK(0, 1, 0));
        }
    }
    

    next_bp = bp;
    return bp;                                          //현재의 bp값을 반환한다.
}

//extend_heap 함수는 힙이 초기화 될 때와 mm_malloc이 적당한 맞춤 fit을 찾지 못했을 때 호출된다.
static void *extend_heap(size_t words) // 매개변수로 words를 받아 void형 포인터를 반환한다. 
{
    char *bp;                           //블록을 가리키는 포인터 bp를 선언
    size_t size;                       //size_t는 부호 없는 정수 타입(unsigned int 또는 unsigned long)이다. 
    size_t prev_alloc;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;       //words가 짝수면 0, 홀수면 1 ; 홀수면 words + 1에 * WSIZE; 짝수면 words * WSIZE;
    prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(mem_heap_hi() + 1)));     // 이전 블록의 할당 여부를 확인한다. (에필로그의 헤더 포인터로 이동)
    if((long)(bp = mem_sbrk(size)) == -1)                           //size만큼 힙을 할당하고 할당에 성공하면 확장 전(힙의 끝을 가리키는)힙의 포인터(void* 타입)를 반환한다.                    
        return NULL;                                                //포인터를 정수 long으로 변환해서 -1과 비교한다.
        //할당되지 않았다면 NULL을 반환한다.
    PUT(HDRP(bp), PACK(size, 0, prev_alloc));                                 //PACK(size와 alloc을 받아 둘을 합친다.) 여기서는 alloc을 0으로 한다. HDRP 메크로를 사용해 bp의 헤더를 찾는다. 헤더에 PACK 한 값을 대입한다.
    PUT(FTRP(bp), PACK(size, 0, prev_alloc));                                   //PACK(size와 alloc을 받아 둘을 합친다.) 여기서는 alloc을 0으로 한다. FTRP 메크로를 사용해 bp의 풋터를 찾는다. 풋터에 PACK 한 값을 대입한다
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1, 0));                           //PACK(여기서 alloc을 1으로 설정한 값) 다음의 bp를 찾는다. 다음 bp의 헤더를 alloc 1로 설정한다. 새 에필로그 블록의 헤더가 된다.
    
    bp = coalesce(bp);
    next_bp = bp;
    return bp;                                            //coalesce(bp)을 호출한다. coalesce 함수는 두 개의 가용블록을 통합하고 통합된 블록 포인터를 리턴한다. 앞 부분을 확인해서 합친다.
}

int mm_init(void)
{   
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1)            //heap_listp에 4워드 사이즈를 할당한다.    
        return -1;                                                  //mem_sbrk 함수가 반환한 값이 -1이라면 -1을 반환
    PUT(heap_listp, 0);                                             //heap_listp가 가리키는 워드에 0을 저장한다. (패딩용 워드 0을 저장한다. 8바이트 정렬 목정)
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1, 1));                 //PACK(더블 워드 사이즈와 1(할당됨))값을 한 워드를 지난 포인터의 워드에 대입한다.(프롤로그 헤더)
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1, 1));                 //PACK(더블 워드 사이즈와 1(할당됨))값을 두 워드를 지난 포인터의 워드에 대입한다.(프롤로그 풋터)
    PUT(heap_listp + (3*WSIZE), PACK(0, 1, 1));                     //PACK(0의 사이즈와 1(할당됨))값을 세 워드를 지난 포인터의 워드에 대입한다. (에필로그 헤더)
    heap_listp += (2*WSIZE);                                        //heap_listp에 두블록의 값을 더한다. (프롤로그 블록의 payload 시작부분을 가리킨다.)

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)                       //extend_heap함수는 힙할당에 실패하면 NULL을 반환한다.
        return -1;                                                  //확장에 실패 했을 때 -1을 반환한다.
    return 0;                                                       //정상적인 동작이 끝나면 0을 반환한다.
}

static void *next_fit(size_t asize)
{
    void *bp;   //void형 포인터 bp를 선언
    bp = next_bp;
    if(next_bp == NULL)
    {
        for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))   //heap의 시작 주소로부터 에필로그 헤더까지 반복한다. bp을 다음 bp로 변환하면서 이동
        {
            if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))       //현재 bp가 할당되지 않았고 요청한 사지ㅡ보다 크거나 같으면
            {
                next_bp = NEXT_BLKP(bp);
                return bp;                                                  //현재 bp를 반환한다.
            }
        }
        return NULL;  
    }
    else
    {
        for(; GET_SIZE(HDRP(bp)) > 0;  bp = NEXT_BLKP(bp))
        {
            if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            {
                next_bp = NEXT_BLKP(bp);
                return bp;
            }
        }
    
        for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))   //heap의 시작 주소로부터 에필로그 헤더까지 반복한다. bp을 다음 bp로 변환하면서 이동
        {
            if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))       //현재 bp가 할당되지 않았고 요청한 사지ㅡ보다 크거나 같으면
            {
                next_bp = NEXT_BLKP(bp);
                return bp;                                                  //현재 bp를 반환한다.
            }
        }
        return NULL;     //모든 탐색이 끝나고 해당 크기가 없다면 NULL을 반환
    }
                                                   
}

//할당 할 블록의 나머지 부분이 최소 블록 크기보다 크거나 같을 경우 분할하는 함수
static void place(void *bp, size_t asize)               //bp와 asize를 매개변수로 받는다.
{
    size_t csize = GET_SIZE(HDRP(bp));                  //csize는 현재 블록의 사이즈

    if((csize - asize) >= (2*DSIZE))                    //현재 블록의 사이즈에 할당 할 사이즈를 뺀 값이 2개의 더블워드드(16바이트)보다 크거나 같을 때
    {
        PUT(HDRP(bp), PACK(asize, 1, GET_PREV_ALLOC(HDRP(bp))));   

        bp = NEXT_BLKP(bp);                             //bp는 다음 bp를 가리킨다.
        PUT(HDRP(bp), PACK(csize - asize, 0, 1));          //PACK(분할된 사이즈) 헤더에 값을 대입 (새로운 헤더 생성)
        PUT(FTRP(bp), PACK(csize - asize, 0, 1));          //PACK 값을 풋터에 워드에 대입한다. (기존의 풋터)
        next_bp = bp;
    }
    else                                                //나머지 부분이 최소 블록보다 작을 경우
    {                                                   //전부를 할당한다.
        PUT(HDRP(bp), PACK(csize, 1, GET_PREV_ALLOC(HDRP(bp))));
        // 다음 블록 prev_alloc 업데이트
        void *next_bp = NEXT_BLKP(bp);
        if (GET_SIZE(HDRP(next_bp)) != 0) 
        {
            size_t next_header = GET(HDRP(next_bp));
            PUT(HDRP(next_bp), (next_header | 0x2)); // prev_alloc = 1로 만든다
        } 
        else 
        {
            PUT(HDRP(next_bp), PACK(0, 1, 1)); // 에필로그 헤더
        }
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
//malloc 

//요청한 size의 메모리를 할당하고 해당 메모리의 시작을 가리키는 포인터를 반환하는 함수
void *mm_malloc(size_t size)                                
{
    size_t asize;           //asize선언 (할당 요청을 위한 정렬된 블록 크기)
    size_t extendsize;      //extendsize 선언 (힙 확장을 위한 크기)
    char *bp;               //bp 포인터 선언 (블록 포인터)

    if(size == 0)           //size가 0이면
        return NULL;        //NULL을 반환
    
    if(size <= DSIZE)       //size가 DSIZE(8바이트) 이하이면
        asize = 2*DSIZE;    //최소 블록 크기(16바이트)로 설정
    else                    
        asize = DSIZE * ((size + (DSIZE) + (DSIZE -1)) / DSIZE);    //요청 크기에 오버헤드(헤더 + 풋터) 추가 후, 8바이트 단위로 올림 정렬하여 asize 계산
    
    //요청 크기 이상인 가용 블록 찾기
    if((bp = next_fit(asize)) != NULL)              //bp에 asize를 매개변수로 find_fit을 한 값을 대입, 해당 값이 NULL이 아닐때
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

/*
 * mm_free - Freeing a block does nothing.
 */
// 블록을 가용 상태로 표시하고, 인접 가용 블록들과 통합하는 함수
void mm_free(void *bp)                   
{
    size_t size = GET_SIZE(HDRP(bp));           // 현재 블록 헤더에 기록된 전체 블록 크기

    PUT(HDRP(bp), PACK(size, 0, GET_PREV_ALLOC(HDRP(bp))));  // 블록 헤더에 (크기, 미할당 상태 0)을 기록한다
    PUT(FTRP(bp), PACK(size, 0, GET_PREV_ALLOC(HDRP(bp))));  // 블록 풋터에도 (크기, 미할당 상태 0)을 기록한다

    // 다음 블록 prev_alloc 업데이트
    void *next_bp = NEXT_BLKP(bp);
    if (GET_SIZE(HDRP(next_bp)) != 0) {
        size_t next_header = GET(HDRP(next_bp));
        PUT(HDRP(next_bp), (next_header & ~0x2)); // prev_alloc = 0으로 만든다
    } else {
        PUT(HDRP(next_bp), PACK(0, 1, 0)); // 에필로그
    }

    coalesce(bp);                               //경계 태그 연결을 사용해서 인접 가용 블록들과 통합
}       

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// 할당한 메모리의 사이즈를 변경하는 함수
void *mm_realloc(void *ptr, size_t size)        //ptr과 새로 요청하는 전체 size를 매개변수로 받는다.
{
    if(ptr == NULL)                             //ptr이 NULL이면
        return mm_malloc(size);                 //malloc한 값의 포인터를 반환한다.

    void *oldptr = ptr;                         //기존 메모리 블록 포인터를 oldptr에 저장
    void *newptr;                               //새로 할당할 블록 포인터
    size_t copySize;                            //복사할 데이터 크기

    newptr = mm_malloc(size);                   //새로운 size만큼 메모리를 할당하고, 포인터를 newptr에 저장
    if (newptr == NULL)                         //할당 할 수 없다면 NULL을 반환
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));          //oldptr 헤더에 저장된 블록 전체 크기를 copySize에 대입

    if (size < copySize)                        //새로 요청한 크기가 기존보다 작다면
        copySize = size;                        //복사할 크기를 새 요청 크기로 한다.

    memcpy(newptr, oldptr, copySize);           //복사할 목적지, 복사할 소스, 복사할 바이트 수 (복사된 메모리의 시작주소를 반환)
    mm_free(oldptr);                            //기존 블록 메모리 해제
    return newptr;                              //새로 할당된 포인터 반환
}