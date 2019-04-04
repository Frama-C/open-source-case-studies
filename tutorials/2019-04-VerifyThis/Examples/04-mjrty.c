unsigned mjrty(unsigned* a, unsigned length) {
  unsigned cand = a[0];
  unsigned cnt = 1;
  for(unsigned i=1; i<length; i++) {
    if (cnt == 0) {
      cand = a[i];
      cnt = 1;
    } else {
      if (a[i] == cand) cnt++;
      else cnt--;
    }
    if (cnt>length/2) { return cand; }
  }
  cnt = 0;
  for (unsigned i=0; i<length; i++) {
    if (a[i] == cand) cnt++;
    if (cnt>length/2) {
      return cand; }
  }
  return 0;
}
