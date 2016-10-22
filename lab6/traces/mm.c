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

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "gcompiler",
    /* First member's full name */
    "Xinyi Gong",
    /* First member's WUSTL key */
    "gongxinyi",
    /* Second member's full name (leave blank if none) */
    "Yuan Gao",
    /* Second member's WUSTL key (leave blank if none) */         /******* changed this *********/
    "gao.yuan"
};


//basic constants and macros from book page 857
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  	(GET(p) & ~0x7)
#define GET_ALLOC(p)	(GET(p) & 0x1)              

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
//line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and prev blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))      //bp+ blocksize = nextbp



/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */

//rounds up!!!!!!!! by clearing the last three bits.
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


#define MIN_BLOCK_SIZE 16         //4 words header + footer + pred + succ
#define INIT_LIST_SIZE 24         //padding+prologue header+prologue footer + prologue pointer*2 + epilogue header
//get the pointer that points to the next free block, stored in bp / or bp+DSIZE.
#define NEXT_FREE(bp)   (*(void **)(bp + WSIZE))
#define PREV_FREE(bp)   (*(void **)(bp))


static void* heap_listp;
static void* free_listp;



//implement LIFO
static void LIFO_add(void *bp) {
    
    //overwrite bp's two pointers
    NEXT_FREE(bp) = free_listp;  //free_listp is the old starting point.
    PREV_FREE(free_listp) = bp;
    PREV_FREE(bp) = NULL;  //first block
    
    //update free_listp;
    free_listp = bp;
}


//implement LIFO
//after allocate a free block, or coalesced.
static void LIFO_delete(void *bp) {
    
    if (PREV_FREE(bp) == NULL) {
        //update the first block
        free_listp = NEXT_FREE(bp);
        PREV_FREE(NEXT_FREE(bp)) = NULL;
    }
    
    else {
        NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
        PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
        
        //NEXT_FREE(bp) = NULL;
        //PREV_FREE(bp) = NULL;
    }

}


//coalesce  book page 860
static void *coalesce(void *bp) {
    
    size_t previous_alloc = GET_ALLOC((char *)bp - DSIZE) || PREV_BLKP(bp) == bp;
    //size_t previous_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    
    //old size
    size_t size = GET_SIZE(HDRP(bp));
    
    //case 1. Both are allocated
    if (previous_alloc && next_alloc) {
        
        //implement LIFO. add this free block to the first block of list.
        LIFO_add(bp);
    }
    
    //case 2. Next is free.
    if(previous_alloc && !next_alloc){
        //n+m2
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        //delete the second block from the free list
        LIFO_delete(NEXT_BLKP(bp));
        
        PUT(HDRP(bp), PACK(size, 0));
        
        //after updating bp's size, we can just find footer of bp instead of bp's next.
        PUT(FTRP(bp), PACK(size, 0));
        //add new block
        LIFO_add(bp);
    }
    
    //case 3. Previous block is free.
    else if(!previous_alloc && next_alloc){
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        
        bp = PREV_BLKP(bp);
        //remove previous block
        LIFO_delete(bp);
        
        //update size
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
        LIFO_add(bp);
    }
    
    //case 4. Both are free.
    else if(!previous_alloc && !next_alloc){
        //n+m1+m2
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        //delete prev and next;
        LIFO_delete(PREV_BLKP(bp));
        LIFO_delete(NEXT_BLKP(bp));
        
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
        LIFO_add(bp);
    }
    
    return bp;

    
}




//book page 858
static void *extend_heap(size_t words) {
    
    char *bp;
    size_t size;
    
    //allocate an even number of words
    size = (words % 2 ) ? (words+1) * WSIZE : words * WSIZE;
    
    //for explicit free list, MIN_BLOCK_SIZE may > size after alignment
    if (size < MIN_BLOCK_SIZE) {
        size = MIN_BLOCK_SIZE;
    }
    
    
    if ((long)(bp = mem_sbrk(size)) == -1 ) {
        return NULL;
    }
    
    //update the new heap
    PUT(HDRP(bp), PACK(size, 0));   //new block header
    PUT(FTRP(bp),  PACK(size, 0));  //new block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   //new epilogue header
    
    return coalesce(bp);  // possible coalesce

}



/* 
 * mm_init - initialize the malloc package.
 */
//see book 858
int mm_init(void)
{
    //heap_listp points to the starting padding.
    
    //allocate initial list size
    if ((heap_listp = mem_sbrk(INIT_LIST_SIZE)) == NULL) {
        return -1;
    }
    
    //aligment padding
    PUT(heap_listp, 0);
    
    //prologue block header
    PUT(heap_listp + WSIZE, PACK(MIN_BLOCK_SIZE, 1));
    
    //prologue pred pointer
    PUT(heap_listp + 2*WSIZE, 0);
    PUT(heap_listp + 3*WSIZE, 0); //succ pointer
    
    //prologue block footer
    PUT(heap_listp + MIN_BLOCK_SIZE, PACK(MIN_BLOCK_SIZE, 1));
    
    //epilogue block header
    PUT(heap_listp + WSIZE + MIN_BLOCK_SIZE, PACK(0, 1));
    
    //free_listp points to the initial position
    free_listp = heap_listp + DSIZE;
    
    
    //extend the empty head
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
    
    return 0;
     
    
}


//implement the find_fit function in the book
static void *find_fit(size_t asize) {
   
    //search the free list
    //check if bp is free, and it has larger size than requested asize.
    
    void *bp = free_listp;
    
    while (bp != NULL) {
        if (GET_ALLOC(HDRP(bp)) == 0) { //if free
            if (GET_SIZE(HDRP(bp)) >= asize) {  //if there is enough space
                //we find a sufficiently large free block
                
                return bp;
            }
        }
        
        bp = NEXT_FREE(bp);
        
    }
    
    //fail to break from while = fail to find such bp;
    return NULL;
    
}

//place size into bp block(slicing if necessary)
static void place(void * bp, size_t size) {
 
    //size of free block found
    size_t free_size = GET_SIZE(HDRP(bp));
    int rest_size = free_size - size;
    
    //if the unused free space can hold another minimal block, split bp block.
    if(rest_size >= MIN_BLOCK_SIZE){
        
        //update allocated bit
        //part of the free bp
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));

        //remove bp from the free list
        LIFO_delete(bp);
        
        
        //rest part of the bp that can be used later
        void* restbp = NEXT_BLKP(bp);
        PUT(HDRP(restbp), PACK(rest_size, 0));
        PUT(FTRP(restbp), PACK(rest_size, 0));
        //add restbp to the free list
        coalesce(restbp);
    }
    
    else{
        
        //update allocate bit
        //padding in the payload
        PUT(HDRP(bp), PACK(free_size, 1));
        PUT(FTRP(bp), PACK(free_size, 1));
        
        //remove bp from the free list
        LIFO_delete(bp);
    }

}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

//book page 861
void *mm_malloc(size_t size) {

    
    size_t asize;
    size_t extendedsize;
    void *bp;
    
    if(size == 0) {
        return NULL;
    }
    
    //for an allocated block, we need at least 8 bytes, so +payload+alignment = at least 16 bytes = MIN_BLOCK_SIZE;
    //ALIGN(size) + footer+header
    asize = MAX(ALIGN(size) + DSIZE, MIN_BLOCK_SIZE);
    
    //if we can find a place.
    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    
    //no fit found
    extendedsize = MAX(asize, CHUNKSIZE);
    
    if((bp = extend_heap(extendedsize / WSIZE)) == NULL) {
        return NULL;
    }
    
    place(bp, asize);
    
    return bp;
    
}

/*
 * mm_free - Freeing a block does nothing.
 */
//book page 860
void mm_free(void *ptr) {
    
    if (ptr == NULL) {
        return;    //return nothing
    }
    
    //check if ptr block is allocated
    if (GET_ALLOC(HDRP(ptr)) == 0) {
        return;
    }
    
    size_t size = GET_SIZE(HDRP(ptr));
    
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    coalesce(ptr);
    
}



/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    
    //if pointer is null
    if (ptr == NULL) {
        return mm_malloc(size);
    }
    
    //if size is 0
    if (size == 0) {
        mm_free(ptr);
        
        return ptr;
    }
   
    
    
    size_t old_size = GET_SIZE(HDRP(ptr));
    //aligned requested size;
    size_t new_size = MAX(ALIGN(size) + DSIZE, MIN_BLOCK_SIZE);
    
    if (old_size == new_size) {
        return ptr;
    }
    
    //splice the ptr block
    if (old_size > new_size) {
        
        //same as place function
        int rest_size = old_size - new_size;
        if (rest_size >= MIN_BLOCK_SIZE) {
            PUT(HDRP(ptr), PACK(new_size, 1));
            PUT(FTRP(ptr), PACK(new_size, 1));
            
            //rest of the block that can be freed;
            void* restptr = NEXT_BLKP(ptr);
            PUT(HDRP(restptr), PACK(rest_size, 0));
            PUT(FTRP(restptr), PACK(rest_size, 0));
            mm_free(restptr);
            
            return ptr;
            
        }
        else {
            return ptr;
        }

    }
    
    

    else {   //expand the old ptr block
        
        void *extended_bp;
        
        //if ptr is at the bottom of the current heap
        size_t next_block_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        if (next_block_size == 0) { //epilogue block header
            //extendheap by diff
            size_t diff = new_size - old_size;
            extended_bp = extend_heap(diff / WSIZE);
            
            if (extended_bp == NULL) { //cannot allocate more heap
                return ptr;
            }
            //combine two blocks
            PUT(HDRP(ptr), PACK(new_size, 1));
            PUT(FTRP(ptr), PACK(new_size, 1));
            
            return ptr;
        }
        
        else {
            
            
            //ptr is in the middle of heap, so we have to malloc a new space/or find_fit.
       
            void *bp;
            size_t asize = MAX(ALIGN(new_size) + DSIZE, MIN_BLOCK_SIZE);
            if((bp = find_fit(asize)) != NULL) {
                place(bp, asize);
                memcpy(bp, ptr, old_size);
                mm_free(ptr);
                return bp;
            }
            
            
            
            else { //bp == NULL
                //extend heap
                extended_bp = extend_heap(new_size / WSIZE);
                if (extended_bp == NULL) { //cannot allocate more heap
                    return ptr;
                }
                place(extended_bp, new_size);
                memcpy(extended_bp, ptr, old_size);
                //PUT(HDRP(extended_bp), PACK(new_size, 1));
                //PUT(FTRP(extended_bp), PACK(new_size, 1));
                mm_free(ptr);
                
                return extended_bp;
                
            }
             
            
           
        }
        
        
        
    }
    
    
}














