#include <stdio.h>

struct blk_data
{
 int data[16];
};


int main(int argc, char *argv[])
{
 int i,j;
 int size = atoi(argv[1]);
 printf("Size of struct : %d", (int)sizeof(struct blk_data));

 struct blk_data b_array[8];
 for(i=0; i < size; i=i+1)
 {
   i = i & 7;
   for(j=0; j < 16; j=j+1)
   {
     b_array[i].data[j] = i & j;
     b_array[i].data[j]++;
   }
 }

}
