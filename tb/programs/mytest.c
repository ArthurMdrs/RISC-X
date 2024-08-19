#include <stdio.h>

// Function to calculate the Fibonacci sequence up to n terms
void fibonacci(int n) {
    int first = 0, second = 1, next;

    // printf("Fibonacci sequence:\n");

    for (int i = 0; i < n; i++) {
        if (i <= 1) {
            next = i;
        } else {
            next = first + second;
            first = second;
            second = next;
        }
        // printf("%d ", next);
    }
    // printf("\n");
}

int main() {
    int n = 10;

    // printf("Enter the number of terms: ");
    // scanf("%d", &n);

    fibonacci(n);

    return 0;
}
