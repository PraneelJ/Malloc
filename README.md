# Malloc
Dynammic Memory allocator in C#
Utilizes a segregated list structure with multiple explicit free lists and first fit search for faster memory allocation. 
Uses immediate coalescing to avoid external fragmentation and minimize memory allocation space, time.
Includes a heap consistency checker to check for errors such fragmentation and overlapping of memory blocks.
