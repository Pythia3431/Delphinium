typedef unsigned char uint8_t;

uint8_t check() {
   uint8_t INPUT_A_msg[16];
   uint8_t INPUT_B_p[16];
   uint8_t msg[16];
   uint8_t last_byte;
   uint8_t result = 1;
   for (uint8_t i = 0; i < 16; i++) {
      msg[i] = INPUT_A_msg[i] ^ INPUT_B_p[i];
   }
   last_byte = msg[16-1];
   if (last_byte > 16) {
      result = 0;
      return result;
   }
   for (uint8_t i = 1; i <= (last_byte & 011111); i++) {
      if (msg[16-i] != last_byte) {
         result = 0;
         return result;
      }
   }
   return result;
}
