/*
 * mm.c
 *
 * Name: Xintong Yu  Andrew ID: xintongy
 *  
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* basic constants and macros */
#define WSIZE		8  		/*word and header/footer size (bytes)*/
#define DSIZE		16		/*Double word size (bytes)*/
#define CHUNKSIZE 	(1<<12) /*Extend heap by the amount(bytes)*/
#define MAX(x,y) 	((x)>(y)? (x):(y))

/*Pack a size and allocated bit into a word*/
#define PACK(size, alloc)	((size) | (alloc))

/*Read and write a word at address P*/
#define GET(p)		(*(unsigned long int *)(p))
#define PUT(p, val)	(*(unsigned long int *)(p) = (val))

/*Read the size and allocated fields from address P */
#define GET_SIZE(p)		(GET(p) & ~0x7)
#define GET_ALLOC(p)	(GET(p) & 0x1)

/*Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)	((char *)(bp) - WSIZE)
#define FTRP(bp)	((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous blocks*/
#define NEXT_BLKP(bp) ((char*)(bp)+GET_SIZE(((char*)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp)-GET_SIZE(((char*)(bp)-DSIZE)))
	
static char *heap_listp; /*pointer to the beginning of the heap*/

static void *find_fit(size_t asize);
static void place(void *bp, size_t asize); 
static void *coalesce(void *bp);
static void *extend_heap(size_t words);


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
	/*Create the initial empty heap*/
	if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
		return -1;
	PUT(heap_listp, 0);
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1));
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1));
	PUT(heap_listp + (3*WSIZE), PACK(0,1));
	heap_listp += (2*WSIZE);
	
	/*Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1;
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
	size_t asize; /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	char *bp;
	
	/* Ignore spurious requests */
	if (size == 0)
		return NULL;
		
	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2*DSIZE;
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
		
	/* Search the free list for a fit */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
	}
	
	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize,CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL;
	place(bp, asize);
	return bp;
}

/*
 * find_fit
 */
static void *find_fit(size_t asize){
	/* First fit search */
	void *bp;
	
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
		return bp;
		}
	}
	return NULL; /* No fit */
}

/*
 * place
 */
static void place(void *bp, size_t asize){
	size_t csize = GET_SIZE(HDRP(bp));
	
	if ((csize - asize) >= (2*DSIZE)) {
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 1));
		PUT(FTRP(bp), PACK(csize - asize, 1));
	}
	else{
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}
/*
 * Extend the heap with a new free block
 */
static void *extend_heap(size_t words){
	char *bp;
	size_t size;
	
	/*Allocate an even number of words to maintain alignment*/
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	
	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
	PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	
	/* Coalesce if the previous block was free */
	return coalesce(bp);
}

/*
 * free
 */
void free (void *ptr) {
    if(!ptr) return;
	
	size_t size = GET_SIZE(HDRP(ptr));
	
	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	coalesce(ptr);
}
/*
 * coalesce
 */
static void *coalesce(void *bp){
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	
	if(prev_alloc && next_alloc){ 	/*prev and next block are allocated*/
		return bp;
	}
	
	else if(prev_alloc && !next_alloc){ 	/* next block is free */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp),PACK(size,0));
		PUT(FTRP(bp),PACK(size,0));
	}
	
	else if(!prev_alloc && next_alloc){ 	/* prev block is free */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(FTRP(bp),PACK(size,0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		bp = PREV_BLKP(bp);
	}
	
	else if(!prev_alloc && !next_alloc){ 	/*prev and next are free*/
		size = size + GET_SIZE(HDRP(NEXT_BLKP(bp))) + 
			GET_SIZE(FTRP(PREV_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
		bp = PREV_BLKP(bp);
	}
	return bp;
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  
 */
void *realloc(void *oldptr, size_t size) {
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0) {
		free(oldptr);
		return 0;
	}
	
	/* If oldptr is NULL, then this is just malloc. */
	if(oldptr == NULL) {
		return malloc(size);
	}
	
	newptr = malloc(size);
	
	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
		return 0;
	}
	
	/* If realloc() succeed, Copy the old data. */
	oldsize = *SIZE_PTR(oldptr);
	if(size < oldsize) oldsize = size;
	memcpy(newptr, oldptr, oldsize);

	/* Free the old block. */
	free(oldptr);

	return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size) {
	size_t bytes = nmemb * size;
	void *newptr;

	newptr = malloc(bytes);
	memset(newptr, 0, bytes);

	return newptr;
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
	if(verbose){}
}
