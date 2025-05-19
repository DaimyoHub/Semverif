int main() {
  int x = rand(0, 100);
  bool a =b false;
  if (x > 20) { a =b true; }
  bool b =b false;
  if (x < 80) { b =b true }

  /*
   * Environment's partitions :
   *   - a = false, b = false ==> x in  [0, 100]
   *   - a = false, b = true  ==> x in  [0,  80[
   *   - a = true,  b = false ==> x in ]20, 100]
   *   - a = true,  b = true  ==> x in  ]20, 80[
   */
  if (a && b) {
    assert(!(20 < x && x < 80)); //@KO
  }
}
