/* STRUCTURE OF THE BLOCKS AND HOW THE ALLOCATOR WORKS

The allocator works with a seggregated list structure with 12 explicit lists which store blocks of size 2^n to 2^n-1 each.
The number 12 has been chosen according to the perfomance index score, and performs the best in the range of 1-20 seg lists.

Each block has a minimum block size of 16 bytes.
All blocks have a header and a footer which store the size and allocation status of the block.
Free blocks also store pointers assigned to the previous and next free blocks in the seg list in their payload.

All free lists are modeled as doubly linked lists pointed to by the 12 pointers stored at the start of the heap, one for each free list of variable block size.
The first pointer points to the seg list with the smallest blocks, each consecutive pointer points to a list with greater sized blocks while the last pointer has blocks with sizes only restricted by the memory in available in the heap.
 
The heap is initiallized with padding, a prologue header, footer and an epilogue header.


NOTE : Several Macros and the Functions extend_heap(size_t words), ADD_free(void *bp, size_t size), place(void *bp, size_t asize), mm_init(void) and mm_malloc(size_t size) have been adapted from the CSAPP book. section 9.9.
*/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"



// static variables used to store pointers
static char *heap_listp = 0; // this is used to point to the prologue block at the start of the heap.
static void* freelist_p = 0 ; // this points to the seg list of smallest size and is used to access all the seg lists.

/* MACROS START */
#define WSIZE 4
#define DSIZE 8
#define CHUNKS (1<<5) // minimum size that the heap extends, chosen according to best performance

#define numlists 12 // number of seg lists used ,chosen according to best performance

//NOTE -- SET THIS TO A NON ZERO INTEGER TO RUN THE HEAP CONSISTENCY CHECKER.
#define runheaptest 0

//macro to get the pointer pointing to the first block in a respective seg list, depending on the list number passed to the macro.
#define GETfreelistp(freelistpointer, listnum) *((char**)(freelistpointer +(4*listnum)))

//these are the macros to put and get values from a word
#define PUT(f, val) (*(unsigned int *)(f) = (val))
#define GET(f)  (*(unsigned int *)(f))

// These are used to get the adresses of the next and previous blocks in a particular seg list.
#define GET_NPTR(bp)  (*(char **)(bp + WSIZE))
#define GET_PPTR(bp)  (*(char **)(bp))

// round up to nearest multiple of 8
#define ROUND8(p)  (p%8) ? p + 8 - (p%8) : p

// put a pointer value into two words
#define PUT_PTR(p, ptr)  (*(unsigned int *)(p) = (unsigned int)(ptr))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))


/*read the size, allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*Given bock ptr bp, compute address of its header and footer */
#define HDRP(bp)   ((char *)(bp) - WSIZE)
#define FTRP(bp)   ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)


/* Given block ptr bp,compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// returns the maximum value of the two values passed
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* MACROS END */

//====================================
// Some Function prototypes
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void ADD_free(void *bp, size_t size);
static void deletefree(void* bp);


//====================================

// start of helper functions used to perform the allocator functions

/*
 extend_heap:
 This function is called whenever there isnt enough memory in the heap , or there isnt contiguous spaces in the heap large enough to store a malloc request.
 
*/
static void *extend_heap(size_t words)
{
char *bp;
size_t size;

/*Allocate an even number of words to maintain alignment */
 size = (words % 2) ? (words + 1)*WSIZE : words * WSIZE;
 if ((long)(bp = mem_sbrk(size)) == -1)
   return NULL;

 // take the maximum of
 size = MAX(size, 16);

 /*initialize free block header/footer and the epilogue header*/
 PUT(HDRP(bp), PACK(size, 0));       /*Free Block header*/
 PUT(FTRP(bp), PACK(size, 0));       /*Free Block footer*/
 PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /*New Epilogue header*/

 
 // Add the recently added free block to one of the free lists by calling coalesce.

 /*coalesce if the previous block was free */
 return coalesce(bp);
 }

/*
 ADD_free:
 This function is called to add a new block to one of the seg lists. Blocks are assigned according to their size.
 Every new block is added to the beginning of the seg list, where it is pointed to by one of the 12 seg list pointers at the start of the heap.
 Function looks into the conditions when the block is being added to an empty list and when it is being added to a non-empty list.
*/

 static void ADD_free(void *bp, size_t size)
 {
   int num = 0;
   size_t bsize = size;
     
   // function divides the block size by 2 till it is less than one. Each time incrementing int num.
   //Thus int num represents the index of the seg list that the block should be assigned to.
    
   while ((num < numlists-1) && (bsize > 1)) {
     bsize >>=  1;
     num++;
   }
     
   void *l_ptr = GETfreelistp(freelist_p,num); // points to the beginning of the seg list
      
  
   if(l_ptr){ // if the seg list is not empty
      
     GET_NPTR(bp) = l_ptr;// assign the next pointer of the block to the original first block in the list.
     GET_PPTR(bp) = NULL; // assign the prev pointer of the new block to NUll
     GET_PPTR(l_ptr) = bp; // assign the prev pointer of the old block to the newly added block
            
            
     GETfreelistp(freelist_p,num) = bp; // assign the start of the list to the new block
   }
   else { // if the list was empty
      
     GETfreelistp(freelist_p,num) = bp; // assign the start of the list to the new block
              
     GET_NPTR(bp) = l_ptr; // assign the next pointer of the block to NULL
     GET_PPTR(bp) = NULL; // assign the prev pointer of the new block to NUll
            
   }
          
   return;
      
 }

 /*
 deletefree:
 
 This function is used to delete a node from a particular seg list.
 
 It takes into account the conditions when the block to be removed is at the start of the list, when it is at the end of the list,
 when it is between two blocks and when it is the only block in the list.
 
 */

 static void deletefree(void* bp){
    
    
   // calculate num according to the size of the block, to access the respective seg list.
   int num=0;
   size_t bsize = GET_SIZE(HDRP(bp));
       
   while ((num < numlists-1) && (bsize > 1)) {
           
     bsize >>=  1;
     num++;
   }
    
    
   if (GET_PPTR(bp)){ // if the prev pointer of the block is not NULL, i.e. the block is not the first block in the list.
        
     if(GET_NPTR(bp)){// if the next pointer of the block is not NULL, i.e. the block is not the last block in the list. i.e. block is between two blocks
        
       GET_NPTR(GET_PPTR(bp)) = GET_NPTR(bp);// point the next pointer of the previous block to the next block
       GET_PPTR(GET_NPTR(bp))= GET_PPTR(bp); // point the prev pointer of the next block to the prev block
          
     }
     else{ // block is the last block in the list
       GET_NPTR(GET_PPTR(bp)) = NULL; // point the next pointer of the previous block to NULL
       return;
     }
    
        
   }
   else{ // block is the first block in the list
        
     if(GET_NPTR(bp)){ // block has a block after it
       GETfreelistp(freelist_p,num) = GET_NPTR(bp); // point the start of the list to the next block
       GET_PPTR(GET_NPTR(bp))= NULL; // point the prev pointer of the next block to NULL
          
     }
     else{ // block is the only block in the list
       GETfreelistp(freelist_p,num) = GET_NPTR(bp); // point the start of the list to null
       return;
     }
      
   }
   return;

    
 }

 /*
 place:
 
 This function takes in a pointer to a free block and the size to be allocated. If the block is big enough, it is split and a new block is created, otherwise the entire block is used.
 
 */
 static void *place(void *bp, size_t asize)
 {
        
   size_t csize = GET_SIZE(HDRP(bp)); // get the size of the block
   void* fin = bp;
        
   deletefree(bp); // remove the block from the free list
    
   if ((csize - asize) >= (2*DSIZE)) { // if the size left after allocating the necessary size is big enough to create a new block (>=16 bytes), split the block
         
     PUT(HDRP(bp), PACK(asize, 1));
     PUT(FTRP(bp), PACK(asize, 1));
     fin = NEXT_BLKP(bp);
     PUT(HDRP(fin), PACK(csize-asize, 0));
     PUT(FTRP(fin), PACK(csize-asize, 0));
     ADD_free(fin,csize-asize);
      
   }
   else { // if the block is not big enough, use the entire block
     PUT(HDRP(bp), PACK(csize, 1));
     PUT(FTRP(bp), PACK(csize, 1));
   }
      
   return bp; // returns pointer to the start of the block
 }

 /*
 find_fit:
 
 This function takes in a block size, accesses the seg list on the best fit policy and returns a pointer to a block large enough using first fit within the seg list.
 */
 static void *find_fit(size_t size)
 {
   // get the seg list number according to best fit, using the size of the block.
   int num = 0;
   size_t bsize = size;
     
   while ((num < numlists-1) && (bsize > 1)) {
         
     bsize >>=  1;
     num++;
   }
    
   void * bp = 0;
    
   //loop through the seg list and return a pointer to the first block that fits the required size.
   for ( bp = GETfreelistp(freelist_p,num); bp!=NULL; bp = GET_NPTR(bp) ){
     if (size <= (size_t)GET_SIZE(HDRP(bp)) ) {
       return bp;
     }
   }
    
   return NULL;
 }

 /*
 coalesce:
 
 This function is used to avoid external fragmentation, by coallescing blocks each time a block is freed. (IMMIDIATE COALESCING)
 
 The function takes four cases into account.
 If the neither of the next and previous blocks in the heap are free, it simply adds the current block to a free list and returns.
 If only the next block is free, it extends the block forward, removes the next block from the free list and adds the larger extended block to a free list.
 If only the previous block is free, it extends the block backward, removes the prev block from the free list and adds the larger extended block to a free list.
 If both the prev and next blocks are free, it removes both blocks from the respective seg lists, and adds the larger extended block to a free list.
 
 
 */
 static void * coalesce(void *bp)
 {
    
   size_t blocksize = GET_SIZE(HDRP(bp)); // get size of the current block
   size_t p_status = GET_ALLOC(HDRP(PREV_BLKP(bp))); // get allocation status of the previous block
   size_t n_status = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // get allocation status of the next block
    
    
   if(n_status && p_status){// If the neither of the next and previous blocks in the heap are free, it simply adds the current block to a free list and returns.
      
     ADD_free(bp, blocksize);
     return bp;
              
   }
   else if(n_status && !(p_status)){ // If only the prev block is free
        
     deletefree(PREV_BLKP(bp)); // delete the prev block from free list
        
        
     blocksize += GET_SIZE(HDRP(PREV_BLKP(bp))); // get new block size
        
     PUT(HDRP(PREV_BLKP(bp)), PACK(blocksize, 0)); // put the new size in the header and footer
     PUT(FTRP(bp), PACK(blocksize, 0));
     bp = PREV_BLKP(bp); // assign the pointer to the new start of the block
        
   }
   else if(p_status && !(n_status)){ // if previous block is not free but next block is free
              
     deletefree(NEXT_BLKP(bp)); // delete the next block from free list
              
              
     blocksize += GET_SIZE(HDRP(NEXT_BLKP(bp))); // get new block size
     PUT(HDRP(bp), PACK(blocksize, 0)); // put the new size in the header and footer
     PUT(FTRP(bp), PACK(blocksize, 0));
              
   }
   else {
        
     deletefree(PREV_BLKP(bp)); // delete the prev block from free list
     deletefree(NEXT_BLKP(bp)); // delete the next block from free list
        
     blocksize += GET_SIZE(FTRP(NEXT_BLKP(bp))); // get the new block size
     blocksize += GET_SIZE(HDRP(PREV_BLKP(bp)));
        
        
     PUT(HDRP(PREV_BLKP(bp)), PACK(blocksize, 0));// put the new size in the header and footer
     PUT(FTRP(NEXT_BLKP(bp)), PACK(blocksize, 0));
     bp = PREV_BLKP(bp); // assign the pointer to the new start of the block
        
   }
  
   ADD_free(bp, blocksize); // add the new extended block to a free list
   return bp; // return a pointer to the start of the block
    
 }




 // END OF HELPER FUNCTIONS


 /* 
  * mm_init - initialize the malloc package. NOTE - This function is adapted from the CSAPP BOOK
  */
 int mm_init(void)
 {
   int num; // used to initialize the
       
   freelist_p = mem_sbrk(numlists*WSIZE); // create space at the start of the heap for the pointers to the several seglist (using four bytes each). This size is a multiple of 8 for allignment purpouses.
       
   // initialize all the pointers to the seg lists
   for (num = 0; num < numlists; num++) {
     GETfreelistp(freelist_p, num)= NULL;
   }

   if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
     return -1;
    
   PUT(heap_listp, 0); /* Alignment padding */
   PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
   PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
   PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
   heap_listp += (2*WSIZE);
  
   // extend the heap to allocate the first block in the heap
   if (extend_heap(CHUNKS/WSIZE) == NULL)
     return -1;
    
   return 0;

 }

 /* 
  * mm_malloc - NOTE - This function is adapted from the CSAPP BOOK
 
 This function is used to allocate a block of a double word (8 bytes) allignment.
 If the heap does not have enough memory left, it returns NULL
 
 */
 void *mm_malloc(size_t size)
 {
   size_t adjusted_size;
   size_t extendsize;
   char *bp;
    
   /* Ignore spurious requests*/
    
   if (size == 0)
     return NULL;
    
   /* Adjust block size to include overhead and alignment reqs. */
   if (size <= DSIZE)
     adjusted_size = 2*DSIZE;
   else
     adjusted_size = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
   /* Search the free list for a fit */
    
   if ((bp = find_fit(adjusted_size)) != NULL) {
     
      
     return place(bp, adjusted_size); // place the block to save any unused memory and return a pointer to the start of the new block
    
        
   }
    
   /* No fit found. Get more memory and place the block */
   extendsize = MAX(adjusted_size,CHUNKS);
   if ((bp = extend_heap(extendsize/WSIZE)) == NULL) // if no memory can be assigned, return NULL
     return NULL;
    
        
   return place(bp, adjusted_size); // place the block to save any unused memory and return a pointer to the start of the new block
 }

 /*
  * mm_free - This function takes a pointer to a block , changes its allocation status to free, and calls coalesce to add the free block to the list.
 
 This function also has the call to the heap consistency checker.
 */
 void mm_free(void *ptr)
 {
   // ignore NUll ptr.
   if (ptr == NULL)
     return;
        
   size_t blocksize = GET_SIZE(HDRP(ptr)); // get the size of the block
    
   PUT(FTRP(ptr), PACK(blocksize, 0)); // change the allocation status in the header and footer.
   PUT(HDRP(ptr), PACK(blocksize, 0));
    
    
    
   coalesce(ptr); // coalesce

   // The following code is used to run the heap consistency check.
   // If the test fails, the function prints ERROR, else it prints that the heap check passed.
    
   if(runheaptest){ // function only runs if the MACRO runheaptest has a non zero value.
      
     if(!mm_check()){
       printf("ERROR");
     }
     else{
       printf("All heap consistency tests passed!");
     }
      
   }
  

 }

 /*
  * mm_realloc
 
 Realloc takes several cases into account.
 
 First it checks for whether the pointer is NULL, on which it returns a newly allocated block of size 'size'.
 It then checks if the size requested is negative , on which is simply returns NULL.
 
 It then checks if the size requested is 0 , on which it frees the current block and returns NULL.
 
 ONCE these checks are complete , it moves on to the conditions where the size passed to the function is positive.
 
 If the size passed is equal to the size of the current block, it returns a pointer to the current block.
 
 If the size passed is less than the size of the current block, it checks whether it can accomodate the new size and split the blcok to save space. if it can't split the block, it uses the entire block.
 
 If the size passed is greater than the current block, it checks to see if the block can be coalesced with the next block in memory to accomodate the requested size.
 If the block cannot be coallesced to fit the new size, it allocates a different block by calling mm_malloc and transfers the data of the old block to the new block
 
 
 */
 void *mm_realloc(void *ptr, size_t size)
 {
    
   size = ALIGN(size);
   size_t newbsize = size + DSIZE; // ADD 8 bytes to the size to accomodate for header and footer
   size_t oldbsize = GET_SIZE(HDRP(ptr)); // store the size of the current block
   void* fin = NULL;
   void *bp = ptr;
   void * newblockptr = NULL;
    
    
   if(ptr==NULL){ // if ptr is NULL return mm_malloc(size)
        
     return mm_malloc(size);
   }
    
   if((int)size < 0){ // ignore requests with negative size.
        
     return NULL;
   }
   else if((int)size == 0){ // if size passed is 0, free up the block
      
     mm_free(ptr);
     return NULL;
   }

    
   if (newbsize == oldbsize) { // if size of the new and old block are the same, return the ptr.
     return ptr;
   }
   else if (oldbsize>newbsize){// if current block can accomodate the new size then return the ptr
        
     if((oldbsize-newbsize) <= 2*DSIZE){ // use the entire block if the block size is not big enough to be split.
       return ptr;
     }
     else{ // if the size left after allocating the necessary size is big enough to create a new block (>=16 bytes), split the block
            
       PUT(HDRP(ptr), PACK(newbsize, 1));
       PUT(FTRP(ptr), PACK(newbsize, 1));
       fin = NEXT_BLKP(ptr);
       PUT(HDRP(fin), PACK(oldbsize-newbsize, 0));
       PUT(FTRP(fin), PACK(oldbsize-newbsize, 0));
       ADD_free(fin,oldbsize-newbsize);
       return ptr;
     }

   }
   else { // if the new size connot be accomodated in the current block
    
     size_t blocksize = GET_SIZE(HDRP(bp));
     size_t n_status = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // get allocation status of the next block in memory
     
     size_t newoldbsize = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp)));; // put the new size into the block
        
     if(!(n_status)&&(newoldbsize>=newbsize)){// if the next block in memory is free and the coalesced block can accomodate the new size
            
       deletefree(NEXT_BLKP(bp)); // delete the next block from the seg list
                    
                    
       blocksize += GET_SIZE(HDRP(NEXT_BLKP(bp))); // increase the block size.
       PUT(HDRP(bp), PACK(blocksize, 0)); // store the new block size and allocation status in the new block
       PUT(FTRP(bp), PACK(blocksize, 0));
            
       if(newoldbsize-newbsize < 2*DSIZE){ // use the entire block if the block size is not big enough to be split.
	 PUT(HDRP(bp), PACK(newoldbsize, 1));
	 PUT(FTRP(bp), PACK(newoldbsize, 1));
	 return bp;
       }
       else{ // if the size left after allocating the necessary size is big enough to create a new block (>=16 bytes), split the block
                    
	 PUT(HDRP(bp), PACK(newbsize, 1));
	 PUT(FTRP(bp), PACK(newbsize, 1));
	 fin = NEXT_BLKP(bp);
	 PUT(HDRP(fin), PACK(newoldbsize-newbsize, 0));
	 PUT(FTRP(fin), PACK(newoldbsize-newbsize, 0));
	 ADD_free(fin,newoldbsize-newbsize);
	 return ptr ;
       }
                
      
            
     }
     else{ // if the block cannot be coallesced to accomodate the new size, use another block by calling mm_malloc and transfer the contents of the old block. Then free the old block.

       newblockptr = mm_malloc(newbsize); // assign a new block
            
       if (newblockptr == NULL)
	 return NULL;
            
       memcpy(newblockptr, ptr, newbsize); // transfer contents of old block
       mm_free(ptr); // free the old block
       return newblockptr;
            
     }
        
   }
    
   return NULL;
 
 }

 /*
 // HEAP CONSISTENCY CHECKER-
 
 NOTE -- this function is called from mm_free function. it is only called when the MACRO runheaptest is set to a non zero value
 It checks for the following conditions -
 
 - whether every block in the seggregated lists is actually free
 - whether any two contiguous blocks in the heap are free (External fragmentation )
 - Whether the all the free blocks in the heap are actually in the free list
 
 - whether any two blocks in the heap are overlapping
 - whether any of the blocks in the heap have a size less than the minimum size of 16 bytes.
 */


 int mm_check(void) {
    

   int check = 1 ;  // this  value is set to 0 if any of the heap consistency checks fail!
    
    
   size_t p_status , n_status; // used to check for allocation statuses of blocks
   
   // check for whether every block in the free list is marked as free.
   void * bp = NULL;
   int numcount = 0;
   int seglistnum= 0;
      

   for(seglistnum=0; seglistnum<numlists; seglistnum++) // for every single free list in the seg list structure
     for ( bp = GETfreelistp(freelist_p,seglistnum); bp!=NULL; bp = GET_NPTR(bp) ){ // loop through every free block in the free list. Also increment int numcount to count the number of free blocks in the heap
      
       numcount++; // increment with every block in the free list.
        
       if ( GET_ALLOC(HDRP(bp))) { // check the allocation status of each block in the free list.
	 check = 0;
	 printf("Test failed : block in the free list is not free. ");
       }
        
        
       // check for whether there are any contiguous free blocks in the heap.
       // loop through every free block in the free list, and check the allocation status of its previous and next blocks in the heap, if any of those are not free print the message
        
       p_status = GET_ALLOC(HDRP(PREV_BLKP(bp))); // alocation status of the previous block in memory
       n_status = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // alocation status of the next block in memory
        
       if(!(p_status) || !(n_status)){
            
	 check = 0;
	 printf("Test failed : Contigous blocks of memory detected in the heap. ");
            
       }
        
        
     }
    
   // get the adress of the prologue block at the start of the heap, then increment to traverse through all the blocks in the heap.
   void * blockpointer = heap_listp;
   int count=0;
   int c = 0;
    
   while(GET_SIZE(HDRP(blockpointer))!=0){
        
     if(!GET_ALLOC(HDRP(blockpointer))) // count the number of free blocks in the heap
       count++;
        
     if(FTRP(blockpointer)>HDRP(NEXT_BLKP(blockpointer))){ // if the adress of the footer of a block is less than the adress of the header of the next block, blocks are overlapping.
       check = 0;
       printf("Test failed : ALLOCATED BLOCKS ARE OVERLAPPING");
     }
          
     //check for whether any of the blocks in the heap have a size less than the minimum block size of 16.
        
     if((c>0) && (GET_SIZE(HDRP(blockpointer))<16)){
       check = 0;
       printf("Test failed : ALLOCATED BLOCK SIZE IS LESS THAN THE MINIMUM BLOCK SIZE OF 16 BYTES");
     }
            
        
     blockpointer = NEXT_BLKP(blockpointer);
     c++;
   }
    
    
   // check if all the free blocks in the heap are present in the explicit free list
   if(count!= numcount){
     check = 0;
     printf("Test failed : Number of blocks in the free list does not match the number of free blocks in the heap");
    
   }
    
    
   if(check){ // if all the heap consistency checks passed
        
     return 1; // non zero number returned as heap tests pass.
        
   }
    
   return 0; // if any of the heap consistency checks failed
    
 }

