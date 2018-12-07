int main(int argc, char **argv, char **envp);

static char *argv[] = { "", 0 };
static char *envp[] = { 0 };

void _start(void) {
	__asm("ldr sp, =" STACK);
	main(1, argv, envp);
	while(1);
}
