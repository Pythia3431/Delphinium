typedef unsigned char uint8_t;

uint8_t check() {
   uint8_t INPUT_A_msg[16];
   uint8_t INPUT_B_p[16];
   uint8_t msg[16];
   uint8_t OUTPUT_result = 1;
   for (uint8_t i = 0; i < 16; i++) {
      msg[i] = INPUT_A_msg[i] ^ INPUT_B_p[i];
   }
   switch (msg[16-1]) {
      case 1:
         OUTPUT_result = 1;
         break;
         return OUTPUT_result;
      case 2:
         OUTPUT_result = msg[16-2] == 2;
         break;
         return OUTPUT_result;
      case 3:
         OUTPUT_result = msg[16-2] == 3 && msg[16-3] == 3;
         break;
         return OUTPUT_result;
      case 4:
         OUTPUT_result = msg[16-2] == 4 && msg[16-3] == 4 && msg[16-4] == 4;
         break;
         return OUTPUT_result;
      case 5:
         OUTPUT_result = msg[16-2] == 5 && msg[16-3] == 5 && msg[16-4] == 5 &&
                  msg[16-5] == 5;
         break;
         return OUTPUT_result;
      case 6:
         OUTPUT_result = msg[16-2] == 6 && msg[16-3] == 6 && msg[16-4] == 6 &&
                  msg[16-5] == 6 && msg[16-6] == 6;
         break;
         return OUTPUT_result;
      case 7:
         OUTPUT_result = msg[16-2] == 7 && msg[16-3] == 7 && msg[16-4] == 7 &&
                  msg[16-5] == 7 && msg[16-6] == 7 && msg[16-7] == 7;
         break;
         return OUTPUT_result;
      case 8:
         OUTPUT_result = msg[16-2] == 8 && msg[16-3] == 8 && msg[16-4] == 8 &&
                  msg[16-5] == 8 && msg[16-6] == 8 && msg[16-7] == 8 &&
                  msg[16-8] == 8;
         break;
         return OUTPUT_result;
      case 9:
         OUTPUT_result = msg[16-2] == 9 && msg[16-3] == 9 && msg[16-4] == 9 &&
                  msg[16-5] == 9 && msg[16-6] == 9 && msg[16-7] == 9 &&
                  msg[16-8] == 9 && msg[16-9] == 9;
         break;
         return OUTPUT_result;
      case 10:
         OUTPUT_result = msg[16-2] == 10 && msg[16-3] == 10 && msg[16-4] == 10 &&
                  msg[16-5] == 10 && msg[16-6] == 10 && msg[16-7] == 10 &&
                  msg[16-8] == 10 && msg[16-9] == 10 && msg[16-10] == 10;
         break;
         return OUTPUT_result;
      case 11:
         OUTPUT_result = msg[16-2] == 11 && msg[16-3] == 11 && msg[16-4] == 11 &&
                  msg[16-5] == 11 && msg[16-6] == 11 && msg[16-7] == 11 &&
                  msg[16-8] == 11 && msg[16-9] == 11 && msg[16-10] == 11 &&
                  msg[16-11] == 11;
         break;
         return OUTPUT_result;
      case 12:
         OUTPUT_result = msg[16-2] == 12 && msg[16-3] == 12 && msg[16-4] == 12 &&
                  msg[16-5] == 12 && msg[16-6] == 12 && msg[16-7] == 12 &&
                  msg[16-8] == 12 && msg[16-9] == 12 && msg[16-10] == 12 &&
                  msg[16-11] == 12 && msg[16-12] == 12;
         break;
         return OUTPUT_result;
      case 13:
         OUTPUT_result = msg[16-2] == 13 && msg[16-3] == 13 && msg[16-4] == 13 &&
                  msg[16-5] == 13 && msg[16-6] == 13 && msg[16-7] == 13 &&
                  msg[16-8] == 13 && msg[16-9] == 13 && msg[16-10] == 13 &&
                  msg[16-11] == 13 && msg[16-12] == 13 && msg[16-13] == 13;
         break;
         return OUTPUT_result;
      case 14:
         OUTPUT_result = msg[16-2] == 14 && msg[16-3] == 14 && msg[16-4] == 14 &&
                  msg[16-5] == 14 && msg[16-6] == 14 && msg[16-7] == 14 &&
                  msg[16-8] == 14 && msg[16-9] == 14 && msg[16-10] == 14 &&
                  msg[16-11] == 14 && msg[16-12] == 14 && msg[16-13] == 14 &&
                  msg[16-14] == 14;
         break;
         return OUTPUT_result;
      case 15:
         OUTPUT_result = msg[16-2] == 15 && msg[16-3] == 15 && msg[16-4] == 15 &&
                  msg[16-5] == 15 && msg[16-6] == 15 && msg[16-7] == 15 &&
                  msg[16-8] == 15 && msg[16-9] == 15 && msg[16-10] == 15 &&
                  msg[16-11] == 15 && msg[16-12] == 15 && msg[16-13] == 15 &&
                  msg[16-14] == 15 && msg[16-15] == 15;
         break;
         return OUTPUT_result;
      case 16:
         OUTPUT_result = msg[16-2] == 16 && msg[16-3] == 16 && msg[16-4] == 16 &&
                  msg[16-5] == 16 && msg[16-6] == 16 && msg[16-7] == 16 &&
                  msg[16-8] == 16 && msg[16-9] == 16 && msg[16-10] == 16 &&
                  msg[16-11] == 16 && msg[16-12] == 16 && msg[16-13] == 16 &&
                  msg[16-14] == 16 && msg[16-15] == 16 && msg[16-16] == 16;
         break;
         return OUTPUT_result;
      default:
         OUTPUT_result = 0;
         break;
         return OUTPUT_result;
   }
   return OUTPUT_result;
}
