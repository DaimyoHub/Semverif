void main() {
  int x = rand(0, 100);
  bool b = x > 0;

  if (b) {
    assert(x > 0); //@OK
  }
}
