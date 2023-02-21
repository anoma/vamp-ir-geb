/* Implementation for various functions needed for GEB. Run as follows:
   vamp-ir setup -o params.pp
   vamp-ir compile -u params.pp -s tests/geb.pir -o circuit.plonk
   vamp-ir prove -u params.pp -c circuit.plonk -o proof.plonk
   vamp-ir verify -u params.pp -c circuit.plonk -p proof.plonk
*/

// *** PREAMBLE ***

// Ensure that the given argument is 1 or 0, and returns it
def bool x = { x*(x-1) = 0; x };

// Extract the 16 bits from a number argument
def range16 a = {
    def a0 = bool (fresh ((a\1) % 2));
    def a1 = bool (fresh ((a\2) % 2));
    def a2 = bool (fresh ((a\4) % 2));
    def a3 = bool (fresh ((a\8) % 2));
    def a4 = bool (fresh ((a\16) % 2));
    def a5 = bool (fresh ((a\32) % 2));
    def a6 = bool (fresh ((a\64) % 2));
    def a7 = bool (fresh ((a\128) % 2));
    def a8 = bool (fresh ((a\256) % 2));
    def a9 = bool (fresh ((a\512) % 2));
    def a10 = bool (fresh ((a\1024) % 2));
    def a11 = bool (fresh ((a\2048) % 2));
    def a12 = bool (fresh ((a\4096) % 2));
    def a13 = bool (fresh ((a\8192) % 2));
    def a14 = bool (fresh ((a\16384) % 2));
    def a15 = bool (fresh ((a\32768) % 2));
    a = a0 + 2*a1 + 4*a2 + 8*a3 + 16*a4 + 32*a5 + 64*a6 + 128*a7 + 256*a8 + 512*a9 + 1024*a10 + 2048*a11 + 4096*a12 + 8192*a13 + 16384*a14 + 32768*a15;
    (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, ())
};

// Extract the 15 bits from a number argument
def range15 a = {
    def a0 = bool (fresh ((a\1) % 2));
    def a1 = bool (fresh ((a\2) % 2));
    def a2 = bool (fresh ((a\4) % 2));
    def a3 = bool (fresh ((a\8) % 2));
    def a4 = bool (fresh ((a\16) % 2));
    def a5 = bool (fresh ((a\32) % 2));
    def a6 = bool (fresh ((a\64) % 2));
    def a7 = bool (fresh ((a\128) % 2));
    def a8 = bool (fresh ((a\256) % 2));
    def a9 = bool (fresh ((a\512) % 2));
    def a10 = bool (fresh ((a\1024) % 2));
    def a11 = bool (fresh ((a\2048) % 2));
    def a12 = bool (fresh ((a\4096) % 2));
    def a13 = bool (fresh ((a\8192) % 2));
    def a14 = bool (fresh ((a\16384) % 2));
    a = a0 + 2*a1 + 4*a2 + 8*a3 + 16*a4 + 32*a5 + 64*a6 + 128*a7 + 256*a8 + 512*a9 + 1024*a10 + 2048*a11 + 4096*a12 + 8192*a13 + 16384*a14;
    (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, ())
};

// Range checks for -2^15 <= x < 2^15.
def intRange16 a = {
  range16 (a + 32768)
};

// Range checks for -2^14 <= x < 2^14.
def intRange15 a = {
  range15 (a + 16384)
};

// Check if a number is negative
// Returns 0 iff a < 0 and 1 otherwise
def negative16 a = {
  def (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, ()) = intRange16 a;

  a15
};

// Check if a number is non-negative
def nonNegative16 a = 1 - negative16 a;

// Test if a is less than b
// Returns 0 iff a < b and 1 otherwise
def less16 a b = {
  // Range checks
  intRange15 a;
  intRange15 b;

  negative16 (a - b)
};

// Valid for a >= 0 and b > 0
def mod16 a b = {
  nonNegative16 b = 0;
  def q = fresh (a\b);
  def r = fresh (a%b);
  nonNegative16 r = 0;
  
  a = b * q + r;
  less16 r b = 0;
  
  r
};


// *** GEB's Functions ***

// const -- one parameter within the range of the input variable
def const x y = x;

// id -- identity polynomial
def id x = x;

// + -- sum two polynomials
def sum p q x = p x + q x;

// * -- multiply two polynomials
def prod p q x = p x * q x;

// . -- compose two polynomials; the output polynomial's domain is the domain of the precedent polynomial
def comp p q x = p (q x);

// - -- subtract two polynomials
def sub p q x = p x - q x;

// / -- divide two polynomials
def div p q x = {
  def qx = q x;
  qxi = fresh (1/qx);
  qx * qxi = 1;
  (p x) * qxi
};

// % -- modulo of two polynomials
def pmod16 p q x = {
  mod16 (p x) (q x)
};

// less -- (pointwise) less-than -- inputs f, g, p, q where the output polynomial is x -> if f(x) < g(x) then p(x) else q(x)
def pwLess16 f g p q x = {
  def t = less16 (f x) (g x);
  (1 - t) * (p x) + t * (q x)
};

// Test
pwLess16 (fun x  { x + 10 }) (fun x  { x * x }) (fun x  { x + 1 }) (fun x  { x - 1 }) 2 = 1;

