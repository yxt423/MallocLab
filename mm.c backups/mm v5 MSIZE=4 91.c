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
//#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
# define dbg_printblock(a) printblock(a)
#else
# define dbg_printf(...)
# define dbg_printblock(a)
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
#define WSIZE			4		/*word and header/footer size (bytes)*/
#define DSIZE			8		/*Double word size (bytes)*/
#define CHUNKSIZE		(1<<9)	/*Extend heap by the amount(bytes)*/
#define MIN_BLKSIZE 	2*DSIZE
#define FREE_LIST_NUM	10		/* number of free lists */
#define MAX_NUMBER		(unsigned int)-1
#define MAX(x,y)		((x)>(y)? (x):(y))

/* single word or double word alignment */
#define ALIGNMENT		DSIZE

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*Pack a size and allocated bit into a word*/
#define PACK(size, alloc)	((size) | (alloc))

/*Read and write a word at address P*/
#define GET(p)				(*(unsigned int *)(p))
#define PUT(p, val)			(*(unsigned int *)(p) = (unsigned int)(val))

/*Read a word at address P */
#define PUT_ADDR(p, val)    (*(int *)(p) = (int)(long)(val))

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
#define PREV_F_BLKP(bp) ((int *)((char *)(bp)))
#define NEXT_F_BLKP(bp) ((int *)((char *)(bp) + WSIZE))

char *heap_listp; 	/*pointer to the beginning of the heap*/
char *free_listp; 	/*pointer to the beginning of the explicit free list*/
char *base_addr; 	/*base address of the heap (base + offset = real addr)*/

inline void *find_fit(size_t asize);
inline void place(void *bp, size_t asize); 
inline void *coalesce(void *bp);
inline void *extend_heap(size_t words);
inline void *offset2addr(int offset);
inline void *next_free_block(void *bp);
inline void *prev_free_block(void *bp);

inline void delete_free_block(void *bp);
inline void insert_free_block(void *bp); 
inline int find_free_list_no(size_t size);
inline void *get_list_root(int i);
inline void *get_list_first(int i);

inline int in_heap(const void *p);
inline int aligned(const void *p);
void mm_checkheap(int verbose);
inline int check_freelist(int list_no);
inline void check_freeblock(void* bp);
inline void check_block(void* bp);
inline void printblock(void *bp);

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
	void * bp;
	/*Create the initial empty heap*/
	if((heap_listp = mem_sbrk(FREE_LIST_NUM*DSIZE + 2*DSIZE)) == (void *)-1){
		fprintf(stderr, "mm_init error\n");
		return -1;
	}
	
	/*use the first FREE_LIST_NUM blocks as free list roots*/ 
	free_listp = heap_listp;
	for(int i=0; i<FREE_LIST_NUM; i++){
		char *root = get_list_root(i);
		PUT_ADDR(root, 1); 
		PUT_ADDR(root+WSIZE, 1);
	}
	
	heap_listp += FREE_LIST_NUM*DSIZE;
	PUT(heap_listp, 0);
	heap_listp += DSIZE;
	PUT(heap_listp - WSIZE, PACK(DSIZE,1));
	PUT(heap_listp, PACK(DSIZE,1));
	PUT(heap_listp + WSIZE, PACK(0,1));
	
	dbg_printf("mm_init: free_listp : %p\n",free_listp);
	dbg_printf("mm_init: heap_listp : %p\n",heap_listp);
	
	/*Extend the empty heap with a free block of CHUNKSIZE bytes */
	if ((bp = extend_heap(CHUNKSIZE/WSIZE)) == NULL){
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
	
	dbg_printf("malloc...\n" );
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
	//size_t asize; 
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
	
	/* If size <= old size or the old block has a free block next to it,
     * then just return the oldptr */
	oldsize = GET_SIZE(HDRP(oldptr));
	/*
    if (size <= DSIZE)
		asize = 2*DSIZE;
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
		
	if (asize <= oldsize) {
        place(oldptr, asize);
        return oldptr;
    }
	else if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr)))){
		dbg_printf("realloc: the old block has a free block next to it.\n");
		dbg_printf("oldsize=%d, ",oldsize);
		size_t nsize = GET_SIZE(HDRP(NEXT_BLKP(oldptr))) + oldsize;
		dbg_printf("nsize=%d\n",nsize);
		if (nsize > asize) {
			delete_free_block(NEXT_BLKP(oldptr));
			PUT(HDRP(oldptr), PACK(nsize, 1));
			PUT(FTRP(oldptr), PACK(nsize, 1));
			place(oldptr, asize);
			return oldptr;
		}
	}
	*/
	newptr = malloc(size);
	
	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
		return 0;
	}
	
	/* Copy the old data. */
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
inline void *find_fit(size_t asize){
	/* First fit search */
	void *bp;
	int free_list_no = find_free_list_no(asize);
	
	dbg_printf("start find_fit in line %d, with size %d\n",free_list_no,(int)asize);
	
	for(int i = free_list_no; i < FREE_LIST_NUM; i++){
		char *root = get_list_root(i);
		for(bp = next_free_block(root); bp != (void*)1; bp = next_free_block(bp)){
			if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ 
				dbg_printf("find_fit in line %d\n",i);
				return bp;
			}
		}
	}
	dbg_printf("can't find_fit.\n");
	return NULL; /* No fit */
}

/*
 * place
 */
inline void place(void *bp, size_t asize){  
	size_t csize = GET_SIZE(HDRP(bp));
	int is_realloc = GET_ALLOC(HDRP(bp));
	
	if ((csize - asize) >= (2*DSIZE)) {  
		if (!is_realloc)
			delete_free_block(bp);
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		
		dbg_printf("place: %d to %d\n",(int)(HDRP(bp)-heap_listp),(int)(FTRP(bp)-heap_listp+WSIZE));
		dbg_printblock(bp);
		
		//PUT(NEXT_BLKP(bp), prev_free_block(bp));
		//PUT(NEXT_BLKP(bp) + WSIZE, next_free_block(bp));
		
		
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		
		insert_free_block(bp);
	}
	else{
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		if (!is_realloc)
			delete_free_block(bp);
	}
}

/*
 * Extend the heap with a new free block
 */
inline void *extend_heap(size_t words){
	char *bp;
	size_t size;
	
	/*Allocate an even number of words to maintain alignment*/
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	
	if (((long)(bp = mem_sbrk(size))) == -1){
		fprintf(stderr, "extend_heap: mem_sbrk error\n");
		return NULL;
	}
	
	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
	PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	
	dbg_printf( "extend_heap: heap extendted to %d\n",(int)(NEXT_BLKP(bp)-heap_listp));
	dbg_printblock(bp);
	
	/* Coalesce if the previous block was free */
	return coalesce(bp);
}

/*
 * free
 */
void free (void *bp) {
	dbg_printf("free...\n" );
    if(!bp) return;
	size_t size = GET_SIZE(HDRP(bp));
	dbg_printf("free: %d to %d\n",(int)(HDRP(bp)-heap_listp),(int)(FTRP(bp)-heap_listp));
	
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * coalesce
 */
inline void *coalesce(void *bp){
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	
	/*prev and next block are allocated*/
	if(prev_alloc && next_alloc){ 	
	}
	/* next block is free */
	else if(prev_alloc && !next_alloc){ 	
		delete_free_block(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp),PACK(size,0));
		PUT(FTRP(bp),PACK(size,0));
	}
	/* prev block is free */
	else if(!prev_alloc && next_alloc){ 	
		delete_free_block(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp),PACK(size,0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		bp = PREV_BLKP(bp);
	}
	/*prev and next are free*/
	else{ 	
		delete_free_block(PREV_BLKP(bp));
		delete_free_block(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
		bp = PREV_BLKP(bp);
	}
	
	insert_free_block(bp);	
	return bp;
}

/********* manipulating free lists *************/

/*
 * Delete free block
 * Delete one free block from the free list
 */
inline void delete_free_block(void *bp ){
	char *prevp = prev_free_block(bp);
	char *nextp = next_free_block(bp);
	
	dbg_printf("delete_free_block...\n");
	PUT_ADDR(prevp + WSIZE, nextp);
	if(nextp != (void*)1)
		PUT_ADDR(nextp, prevp);
	
	dbg_printf("delete_free_block: list no %d,\n",find_free_list_no(GET_SIZE(HDRP(bp))) );
	dbg_printblock(bp);
}

/*
 * Insert free block (LIFO)
 * Insert one free block to the root point of an appropriate free list
 */
inline void insert_free_block(void *bp){
	int i = find_free_list_no(GET_SIZE(HDRP(bp)));
	char *root = get_list_root(i);
	char *nextp = get_list_first(i);
	
	PUT_ADDR(bp, root);
	PUT_ADDR(bp + WSIZE, nextp);
	PUT_ADDR(root + WSIZE, bp);
	if(nextp != (void*)1)
		PUT_ADDR(nextp, bp);
	
	dbg_printf("insert_free_block: list no %d \n",i);
	dbg_printblock(bp);
}

/*
 * find_free_list_no - given sieze, compute free_list_no
 */
inline int find_free_list_no(size_t size){
	/*
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
	*/
	int block = size / DSIZE;
    if (block <= 4) 
        return 0;
    if (block <= 8) 
        return 1;
    if (block <= 16) 
        return 2;
    if (block <= 32) 
        return 3;
    if (block <= 64) 
        return 4;
    if (block <= 128) 
        return 5;
    if (block <= 256) 
        return 6;
    if (block <= 512) 
        return 7;
    if (block <= 1024) 
        return 8;
    //if (block <= 2048) 
    //    return 9;
    //if (block <= 4096) 
    //    return 10;
    return 9;
}

/*
 * get_list_root - Get root node for list i
 */
inline void *get_list_root(int i){
    return free_listp + i*DSIZE;
}
/*
 * get_list_first - Get the first node for list i
 */
inline void *get_list_first(int i){
	void * root = get_list_root(i);
    return next_free_block(root);
}

/********* manipulating address *************/

/*
 * offset2addr - restore the offset to address
 */
inline void *offset2addr(int offset){
    if (offset != 1) 
        return (void *)((long int)offset | 0x800000000);
    else 
        return (void *)1;
}

/*
 * next_free_block - Given block bp, get next free block
 */
inline void *next_free_block(void *bp){
    int offset = *NEXT_F_BLKP(bp);
    return offset2addr(offset);
}

/*
 * prev_free_blck - Given block bp, get previous block
 */
inline void *prev_free_block(void *bp){
    int offset = *PREV_F_BLKP(bp);
    return offset2addr(offset);
}

/*
 * get_addr - Get the address stored in address bp
 */
inline void *get_addr(void *bp){
    int offset = GET(bp);
    return offset2addr(offset);
}

/**************** debugging tools ****************/

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
inline int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
inline int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
	void *bp;
	int free_block_counter_1 = 0;
	int free_block_counter_2 = 0;
	
	/*Check prologue blocks*/
	if ( GET_SIZE(HDRP(heap_listp)) != DSIZE || GET_ALLOC(HDRP(heap_listp)) != 1 )
		fprintf(stderr, "checkheap: heap prologue block error\n");
	
	/*Check epilogue block*/
	bp = mem_heap_hi() + 1 - WSIZE;
	if((GET_SIZE(bp) != 0) || (GET_ALLOC(bp) != 1)){
		fprintf(stderr, "checkheap: heap epilogue block error,");
		if(verbose) printblock(bp);
	}
	
	/*Check free_listp root*/
	if ((free_listp + FREE_LIST_NUM*DSIZE + DSIZE) != heap_listp){
		fprintf(stderr, "checkheap: free_listp error. \n");
		fprintf(stderr, "free_listp=%p, heap_listp=%p\n",free_listp,heap_listp);
	}
	
	/*Check each block*/
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		check_block(bp);
		
		/*Check each free block*/
		if(GET_ALLOC(HDRP(bp)) == 0){
			free_block_counter_1++; /*Count free blocks by iterating through every block*/
			check_freeblock(bp);
		}
	}
	
	free_block_counter_2 = 0;
	for(int i=0; i<FREE_LIST_NUM; i++){
		free_block_counter_2 += check_freelist(i);
	}
	/*Check counters consistancy*/
	if(free_block_counter_1 != free_block_counter_2){
		fprintf(stderr, "checkheap: free_block_counter doesn't match, ");
		fprintf(stderr, "counter_1=%d, counter_2=%d.\n",free_block_counter_1,free_block_counter_2);
	}
}

/*
 * check_block - check content of each block
 */
inline void check_block(void* bp){
	if(in_heap(bp) != 1)	/*Check point in the heap */
		fprintf(stderr, "checkheap: pointer is not in the heap\n");
	if(aligned(bp) != 1)	/*Check block's address alignmen */
		fprintf(stderr, "checkheap: pointer is not aligned.\n");
		
	/*Check each block's header and footer*/
	if(GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp))){
		fprintf(stderr, "checkheap: size of h&f doesn't match.\n");
		printblock(bp);
	}
	if(GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))){
		fprintf(stderr, "checkheap: alloc of h&f doesn't match.\n");
		printblock(bp);
	}
}

/*
 * check_freeblock - check content of each free block
 */
inline void check_freeblock(void* bp){
	/*Check coalescing*/
	if( GET_ALLOC(HDRP(PREV_BLKP(bp))) == 0 || GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0 )
		fprintf(stderr, "checkheap: two consecutive free blocks in the heap.\n");
	
	/*All free list pointers point in the heap*/
	if( (in_heap(get_addr(bp)) != 1)   ||
		((in_heap(get_addr(bp + WSIZE)) != 1) && (get_addr(bp + WSIZE) != NULL))   ){
		fprintf(stderr, "checkheap: free list pointer doesn't point in the heap.\n");
		fprintf(stderr, "mem_heap_hi()=%p, mem_heap_lo()=%p, \n",mem_heap_hi(),mem_heap_lo());
		fprintf(stderr, "get_addr(bp)=%p, get_addr(bp + WSIZE)=%p, \n",get_addr(bp),get_addr(bp + WSIZE));
	}
	
	/* next/previous pointers are consistent */
	if(  next_free_block(prev_free_block(bp)) != bp ){
		fprintf(stderr, "checkheap: pred: pred and succ doesn't match.\n");
		fprintf(stderr, "pred's next=%p, bp's pred = %p\n",next_free_block(prev_free_block(bp)),get_addr(bp));
		fprintf(stderr, "pred's address=%p, bp's address=%p\n",prev_free_block(bp),bp);
	}
	if(get_addr(bp + WSIZE) != NULL && prev_free_block(next_free_block(bp)) != bp)
		fprintf(stderr, "checkheap: succ: pred and succ doesn't match.\n");
}

/*
 * check_freelist - check each free list
 */
inline int check_freelist(int i){
	/*Check each free list*/
	char * bp;
	int block_counter = 0;
	if(get_list_first(i) == NULL)
		return 0;
		
	int last_free_block_counter = 0;
	unsigned int min_size = (1<<(i+4))+1;
	unsigned long int max_size = 1<<(i+5);
	if(i == 0)
		min_size = 2*DSIZE;
	if(i == (FREE_LIST_NUM-1))
		max_size = MAX_NUMBER;
	
	for(bp = get_list_first(i); bp != (void*)1; bp = next_free_block(bp)){
		/*Count free blocks by traversing free list */
		block_counter++;
			
		if(get_addr(bp + WSIZE) == (void*)1)
			last_free_block_counter++;
			
		/*All blocks in each list bucket fall within bucket size range*/
		/*
		size_t size = GET_SIZE(HDRP(bp));
		if(size < min_size || size > max_size){
			fprintf(stderr, "checkheap: free block in wrong list.\n");
			fprintf(stderr, "size=%d,FREE_LIST_NUM=%d.\n",(int)size,find_free_list_no(size));
		}
		*/
	}
	
	if(last_free_block_counter != 1)
		fprintf(stderr, "checkheap: last_free_block_counter=%d\n",last_free_block_counter);

	return block_counter;
}
/*
 * printblock - print address, size and alloc of a block
 */
inline void printblock(void *bp){
	printf("bp=%p,h_a = %d, f_a = %d, h_s = %d, f_s = %d. \n",bp,
		GET_ALLOC(HDRP(bp)),GET_ALLOC(FTRP(bp)),GET_SIZE(HDRP(bp)),GET_SIZE(FTRP(bp)));
	if(GET_ALLOC(HDRP(bp)) == 0)
		printf("pred = %p, succ = %p\n",prev_free_block(bp),next_free_block(bp));
}
