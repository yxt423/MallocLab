/*
 * mm.c
 *
 * Name: Xintong Yu  Andrew ID: xintongy
 *  
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include "mm.h"
#include "memlib.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

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



/* basic constants and macros */
#define WSIZE			8		/*word and header/footer size (bytes)*/
#define DSIZE			16		/*Double word size (bytes)*/
#define CHUNKSIZE		(1<<12)	/*Extend heap by the amount(bytes)*/
#define FREE_LIST_NO	8		/* number of free lists */
#define MAX_NUMBER		(unsigned long int)-1
#define MAX(x,y)		((x)>(y)? (x):(y))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 		8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/*Pack a size and allocated bit into a word*/
#define PACK(size, alloc)	((size) | (alloc))

/*Read and write a word at address P*/
#define GET(p)		(*(unsigned long int *)(p))
#define PUT(p, val)	(*(unsigned long int *)(p) = (unsigned long int)(val))

/*Read a word at address P and convert to a void pointer*/
#define GET_VP(p)		(void *)GET(p)

/*Read the size, allocated fields or list boundary mark from address P */
#define GET_SIZE(p)		(GET(p) & ~0x7)
#define GET_ALLOC(p)	(GET(p) & 0x1)
#define GET_BOUNDARY(p)	(GET(p) & 0x1)

/*Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)		((char *)(bp) - WSIZE)
#define FTRP(bp)		((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous blocks*/
#define NEXT_BLKP(bp) 	((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) 	((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
	
/*Given block ptr bp, read address of next and previous free blocks*/
#define PREV_F_BLKP(bp) (char *)GET(bp)
#define NEXT_F_BLKP(bp) (char *)GET((char*)(bp) + WSIZE)

static char *heap_listp; 	/*pointer to the beginning of the heap*/
static char *free_listp; 	/*pointer to the beginning of the explicit free list*/

static void *find_fit(size_t asize);
static void place(void *bp, size_t asize); 
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void delete_free_block(void *bp);
static void insert_free_block(void *bp);
static void *find_free_list(void *bp);
static int find_free_list_no(size_t size);

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
	/*Create the initial empty heap*/
	if((heap_listp = mem_sbrk((FREE_LIST_NO + 4)*WSIZE)) == (void *)-1){
		fprintf(stderr, "mm_init error\n");
		return -1;
	}
	
	/*use the first 8 words for 8 free list pointers*/
	free_listp = heap_listp;
	for(int i=0; i<FREE_LIST_NO; i++){
		PUT(free_listp + (i*WSIZE), 0);
	}
	
	heap_listp += (FREE_LIST_NO*WSIZE);
	PUT(heap_listp, 0);
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1));
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1));
	PUT(heap_listp + (3*WSIZE), PACK(0,1));
	heap_listp += (2*WSIZE);
	//
	fprintf(stderr, "mm_init: heap start from: %p\n",heap_listp);
	fprintf(stderr, "mm_init: free_listp start from: %p\n",free_listp);
	
	/*Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
		fprintf(stderr, "extend_heap in mm_init error\n");
		return -1;
	}
		
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
	if (size <= 0)
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
	oldsize = GET_SIZE(HDRP(oldptr));
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
 * find_fit
 */
static void *find_fit(size_t asize){
	/* First fit search */
	void *bp;
	unsigned long int flp;
	long int free_list_no = find_free_list_no(asize);
	//fprintf(stderr, "start find_fit in line %ld, with size %d\n",free_list_no,asize);//
	
	for(int i = free_list_no; i < FREE_LIST_NO; i++){
		flp = GET(free_listp + (i*WSIZE));
		//fprintf(stderr, "start find_fit! flp=%p,address=%p\n",free_listp + (i*WSIZE),(char*)GET(free_listp + (i*WSIZE)));//
		if(flp == 0)
			continue;
		for(bp = (char *)flp; (unsigned long int)bp != 1;bp = NEXT_F_BLKP(bp)){
			//fprintf(stderr, "bp=%p,size=%lu,next_bp=%p\n",bp,GET_SIZE(HDRP(bp)),NEXT_F_BLKP(bp));
			if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ 
				fprintf(stderr, "find_fit in line %d\n",i);//
				return bp;
			}
		}
		//fprintf(stderr, "can't find_fit in line %d\n",i);
	}
	return NULL; /* No fit */
}

/*
 * place
 */
static void place(void *bp, size_t asize){  
	size_t csize = GET_SIZE(HDRP(bp));
	
	if ((csize - asize) >= (2*DSIZE)) {  
		delete_free_block(bp);
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		
		PUT(NEXT_BLKP(bp), PREV_F_BLKP(bp));
		PUT(NEXT_BLKP(bp) + WSIZE, NEXT_F_BLKP(bp));
		
		//
		fprintf(stderr, "place: %d to %d\n",(int)(HDRP(bp)-heap_listp),(int)(FTRP(bp)-heap_listp+WSIZE));
		
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		
		insert_free_block(bp);
	}
	else{
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		delete_free_block(bp);
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
	if ((long)(bp = mem_sbrk(size)) == -1){
		fprintf(stderr, "extend_heap: mem_sbrk error\n");
		return NULL;
	}
	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
	PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	
	//
	fprintf(stderr, "extend_heap: heap extendted to %d\n",(int)(HDRP(NEXT_BLKP(bp))-heap_listp));
	
	/* Coalesce if the previous block was free */
	return coalesce(bp);
}

/*
 * free
 */
void free (void *bp) {
    if(!bp) return;
	if(bp == heap_listp) return;
	if(bp == (mem_heap_hi() + 1 - WSIZE)) return;
	
	size_t size = GET_SIZE(HDRP(bp));
	
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	
	//
	fprintf(stderr, "free: %d to %d\n",(int)(HDRP(bp)-heap_listp),(int)(FTRP(bp)-heap_listp));
		
	coalesce(bp);
}

/*
 * coalesce
 */
static void *coalesce(void *bp){
	if(bp == heap_listp) return bp;
	if(bp == (mem_heap_hi() + 1 - WSIZE)) return bp; //
	
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	
	/*prev and next block are allocated*/
	if(prev_alloc && next_alloc){ 	
		insert_free_block(bp);
		return bp;
	}
	/* next block is free */
	else if(prev_alloc && !next_alloc){ 	
		delete_free_block(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp),PACK(size,0));
		PUT(FTRP(bp),PACK(size,0));
		insert_free_block(bp);
	}
	/* prev block is free */
	else if(!prev_alloc && next_alloc){ 	
		delete_free_block(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp),PACK(size,0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		bp = PREV_BLKP(bp);
		insert_free_block(bp);
	}
	/*prev and next are free*/
	else{ 	
		delete_free_block(PREV_BLKP(bp));
		delete_free_block(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
		bp = PREV_BLKP(bp);
		insert_free_block(bp);
	}
		
	return bp;
}

/*
 * Delete free block
 * Delete one free block from the free list
 */
static void delete_free_block(void *bp ){
	char *flp;
	
	/*****update pred's pointer*****/
	/*block has predecessor*/
	if (GET_BOUNDARY(bp) != 1){ 			
		PUT(PREV_F_BLKP(bp) + WSIZE, NEXT_F_BLKP(bp));
	}	
	/*no predecessor, has succeeder, uppdate free list p */
	else if (GET_BOUNDARY(bp + WSIZE) != 1){	
		flp = find_free_list(bp);
		PUT(flp, NEXT_F_BLKP(bp));
	}	
	/*no predecessor or succeeder (the only free block was taken)*/
	else{
		flp = find_free_list(bp);
		PUT(flp, 0);
	}
	
	/*****update succ's pointer*****/		
	if (GET_BOUNDARY(bp + WSIZE) != 1) 	 
		PUT(NEXT_F_BLKP(bp), PREV_F_BLKP(bp));
	//
	fprintf(stderr, "delete_free_block: list no %d, size=%ld\n",find_free_list_no(GET_SIZE(HDRP(bp))),GET_SIZE(HDRP(bp)));
}

/*
 * Insert free block (LIFO)
 * Insert one free block to the root point of an appropriate free list
 */
static void insert_free_block(void *bp){
	char *flp = find_free_list(bp);
	
	/*free list uninitialized*/
	if(GET(flp) == 0){				
		PUT(bp, PACK(0,1));
		PUT(bp + WSIZE, PACK(0,1));
		PUT(flp, bp);
	}
	/*free list exist*/
	else{							
		PUT(bp,PACK(0,1));			/*update bp's pred and succ pointer*/
		PUT(bp + WSIZE, flp);
		PUT(GET(flp), bp);			/*update succ's pred pointer*/
		PUT(flp, bp);				/*update free list root*/
	}
	
	//
	fprintf(stderr, "insert_free_block: list no %d, size=%ld\n",find_free_list_no(GET_SIZE(HDRP(bp))),GET_SIZE(HDRP(bp)));
}

/*
 * find_free_list - Given a free blovk,
 * find which list it belongs to, return the list pointer
 */
static void *find_free_list(void *bp){
	size_t size = GET_SIZE(HDRP(bp));
	long int free_list_no = find_free_list_no(size);
	char *flp = free_listp + free_list_no*WSIZE;
	return flp;
}

/*
 * find_free_list_no - compute free_list_no
 * free list block sizes are as follows:
 * 0		1			2			3		
 * 1-32;	33-64;		65-128;		129-256;
 * 4		5			6			7
 * 257-512;	513-1024;	1025-2048;	2049-infinity
 */
static int find_free_list_no(size_t size){
	int free_list_no;
	if(size <= 256){
		if(size <= 64){
			if(size <= 32)
				free_list_no = 0;
			else
				free_list_no = 1;
		}
		else{
			if(size <= 128)
				free_list_no = 2;
			else
				free_list_no = 3;
		}
	}
	else{
		if(size <= 1024){
			if(size <= 512)
				free_list_no = 4;
			else
				free_list_no = 5;
		}
		else{
			if(size <= 2048)
				free_list_no = 6;
			else
				free_list_no = 7;
		}
	}
	return free_list_no;
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
	void *bp;
	int free_block_counter_1 = 0;
	int free_block_counter_2 = 0;
	if(verbose){}
	
	/*Check prologue blocks*/
	if ( GET_SIZE(HDRP(heap_listp)) != DSIZE || GET_ALLOC(HDRP(heap_listp)) != 1 )
		fprintf(stderr, "checkheap: heap prologue block error\n");
	
	/*Check epilogue block*/
	bp = mem_heap_hi() + 1 - WSIZE;
	if((GET_SIZE(bp) != 0) || (GET_ALLOC(bp) != 1)){
		fprintf(stderr, "checkheap: heap epilogue block error,");
		fprintf(stderr, "size=%lu, alloc=%lu\n",GET_SIZE(bp),GET_ALLOC(bp));
	}
	
	/*Check free_listp root*/
	if ((free_listp + (FREE_LIST_NO+2)*WSIZE) != heap_listp){
		fprintf(stderr, "checkheap: free_listp error. \n");
		fprintf(stderr, "free_listp=%p, heap_listp=%p\n",free_listp,heap_listp);
	}
	
	/*Check each block*/
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if(in_heap(bp) != 1)	/*Check point in the heap */
			fprintf(stderr, "checkheap: pointer is not in the heap\n");
		if(aligned(bp) != 1)	/*Check block's address alignmen */
			fprintf(stderr, "checkheap: pointer is not aligned.\n");
			
		/*Check each block's header and footer*/
		if(GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp))){
			fprintf(stderr, "checkheap: size of h&f doesn't match, ");
			fprintf(stderr, "header=%lu, footer=%lu, ",GET_SIZE(HDRP(bp)),GET_SIZE(FTRP(bp)));
			fprintf(stderr, "header_a=%lu, footer_a=%lu\n",GET_ALLOC(HDRP(bp)),GET_ALLOC(FTRP(bp)));
		}
		if(GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp)))
			fprintf(stderr, "checkheap: alloc of h&f doesn't match.\n");
			
		/***Check each free block****/
		if(GET_ALLOC(HDRP(bp)) == 0){
			free_block_counter_1++; /*Count free blocks by iterating through every block*/
			
			/*Check coalescing*/
			if( GET_ALLOC(HDRP(PREV_BLKP(bp))) == 0 || GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0 )
				fprintf(stderr, "checkheap: two consecutive free blocks in the heap.\n");
			
			/*All free list pointers point in the heap*/
			if( ((in_heap(GET_VP(bp)) != 1) && (GET_BOUNDARY(bp) !=1))  ||
				((in_heap(GET_VP(bp + WSIZE)) != 1) && (GET_BOUNDARY(bp + WSIZE) !=1))   ){
				fprintf(stderr, "checkheap: free list pointer doesn't point in the heap.\n");
				fprintf(stderr, "mem_heap_hi()=%p, mem_heap_lo()=%p, \n",mem_heap_hi(),mem_heap_lo());
				fprintf(stderr, "GET_VP(bp)=%p, GET_VP(bp + WSIZE)=%p, \n",GET_VP(bp),GET_VP(bp + WSIZE));
			}
			
			/* next/previous pointers are consistent */
			if(GET_BOUNDARY(bp) !=1 && NEXT_F_BLKP(PREV_F_BLKP(bp)) != bp ){
				fprintf(stderr, "checkheap: pred: pred and succ doesn't match.\n");
				fprintf(stderr, "NEXT_F_BLKP(PREV_F_BLKP(bp))=%p, bp=%p\n",NEXT_F_BLKP(PREV_F_BLKP(bp)),bp);
			}
			if(GET_BOUNDARY(bp + WSIZE) !=1 && PREV_F_BLKP(NEXT_F_BLKP(bp)) != bp)
				fprintf(stderr, "checkheap: succ: pred and succ doesn't match.\n");
		}
	}
	
	/*Check each free list*/
	free_block_counter_2 = 0;
	for(int i=0; i<FREE_LIST_NO; i++){
		unsigned long int flp = GET(free_listp + i*WSIZE);
		if(flp == 0)
			continue;
			
		int first_free_block_counter = 0;
		int last_free_block_counter = 0;
		unsigned int min_size = (1<<(i+4))+1;
		unsigned long int max_size = 1<<(i+5);
		if(i == 0)
			min_size = 2*DSIZE;
		if(i == (FREE_LIST_NO-1))
			max_size = MAX_NUMBER;
		
		for(bp = (char*)flp; (unsigned long int)bp != 1; bp = NEXT_F_BLKP(bp)){
			/*Count free blocks by traversing free list */
			free_block_counter_2++;
				
			if(GET_BOUNDARY(bp) == 1)
				first_free_block_counter++;
			if(GET_BOUNDARY(bp + WSIZE) == 1)
				last_free_block_counter++;
				
			/*All blocks in each list bucket fall within bucket size range*/
			size_t size = GET_SIZE(HDRP(bp));
			if(size < min_size || size > max_size){
				fprintf(stderr, "checkheap: free block in wrong list.\n");
				fprintf(stderr, "size=%lu,free_list_no=%d.\n",size,find_free_list_no(size));
			}
		}
		
		if(first_free_block_counter != 1)
			fprintf(stderr, "checkheap: first_free_block_counter=%d\n",first_free_block_counter);
		if(last_free_block_counter != 1)
			fprintf(stderr, "checkheap: last_free_block_counter=%d\n",last_free_block_counter);
	}
	
	/*Check counters consistancy*/
	if(free_block_counter_1 != free_block_counter_2){
		fprintf(stderr, "checkheap: free_block_counter doesn't match, ");
		fprintf(stderr, "counter_1=%d, counter_2=%d.\n",free_block_counter_1,free_block_counter_2);
	}
}
