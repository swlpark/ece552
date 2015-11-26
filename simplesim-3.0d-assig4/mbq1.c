#include <stdio.h>

struct blk_data
{
 int data[16];
};


int main(int argc, char *argv[])
{
 int i,j;
 int size = atoi(argv[1]);

 struct blk_data b_array[size];
 for(i=0; i < size; i=i+1)
 {
   for(j=0; j < 16; j=j+1)
   {
     b_array[i].data[j] = i & j;
   }
 }

}
