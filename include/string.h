#pragma once

char *strcpy(char *trg, const char *src) {
  size_t i=0;
  do {
    trg[i] = src[i];
  } while(src[i++]);
  return trg;
}
