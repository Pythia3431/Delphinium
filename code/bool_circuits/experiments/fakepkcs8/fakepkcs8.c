
unsigned int check() {
   unsigned int INPUT_A_msg, INPUT_B_p;
   unsigned int msg = INPUT_A_msg ^ INPUT_B_p;
   unsigned int mask = (1 << 5) - 1;
   unsigned int numbits = msg & mask;
   unsigned int pad = (1 << numbits) - 1;
   return ((msg >> 5) & pad) == pad;
}
