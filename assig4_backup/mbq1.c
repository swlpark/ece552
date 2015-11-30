#include <stdio.h>

struct blk_data {
    long int data[8];
};

int main(int argc, char *argv[]) {
    int i, j;
    int size = atoi(argv[1]);

    struct blk_data barray[size];

    for (i = 0; i < size; i++) {
	for (j = 0; j < 8; j++) {
	    barray[i].data[0] = i ^ j ^ barray[i].data[j];
	}
    }
    
    return 0;
}
