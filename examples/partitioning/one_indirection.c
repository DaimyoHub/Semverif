void main() {
  int x = rand(0, 100);
  bool b =b false;

  if (x > 20) {
    b =b true;
  }

  if (b) {
    /*
     * Without the partitioning domain, the assertion should check as the analyzer does
     * not compute the relation between x and b. The conditional indirection makes the 
     * property opaque from the analyzer's point of view.
     *
     * The partitioning domain exactly keeps a trace of this relation. The assertion
     * should not check using it.
     */
    assert(x <= 20); //@KO
  }
}
