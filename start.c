#include <stdio.h>

int Main();  // note that Main now returns an integer!

int main(int argc, char **argv) {
    printf("Main returned: %d \n", Main());
    return 0;
}
