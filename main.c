#include <stdio.h>

int add(int a, int b){
    return a + b;
}
int main(){
    printf("Hello, World!\n");
    int a = 1;
    int b = 2;
    int c = add(a, b);
    printf("c = %d\n", c);
    return 0;
}
