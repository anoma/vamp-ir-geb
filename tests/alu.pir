// Pair up corresponding elements of each tuple

def zip8
        (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7,ar))))))))
        (b0,(b1,(b2,(b3,(b4,(b5,(b6,(b7,br)))))))) {
    ((a0,b0),((a1,b1),((a2,b2),((a3,b3),((a4,b4),((a5,b5),((a6,b6),((a7,b7),()))))))))
};

// Apply function to each element of tuple

def map8 f (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7,ar)))))))) {
    (f a0,(f a1,(f a2,(f a3,(f a4,(f a5,(f a6,(f a7,()))))))))
};

// Multiply each tuple element by corresponding unit

def combine8 (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7,ar)))))))) {
    a0 + 2*a1 + 4*a2 + 8*a3 + 16*a4 + 32*a5 + 64*a6 + 128*a7
};

// Apply given function to corresponding bit-pairs in bit representation

def bitwise8 g a b {
    def zipped = zip8 (range 8 a) (range 8 b);
    def new_bits = map8 g zipped;
    combine8 new_bits
};

// Definition of xor for domain {0, 1}^2

def bit_xor (a,b) { a*(1-b)+(1-a)*b };

// Definition of bitwise xor for 8 bit values

def xor8 = bitwise8 bit_xor;

// Definition of or for domain {0, 1}^2

def bit_or (a,b) { a + b - a*b };

// Definition of bitwise or for 8 bit values

def or8 = bitwise8 bit_or;

// Definition of and for domain {0, 1}^2

def bit_and (a,b) { a*b };

// Definition of bitwise and for 8 bit values

def and8 = bitwise8 bit_and;

// Definition of bitwise not for 8 bit values

def not8 y { combine8 (map8 (fun x { 1-x }) (range 8 y)) };

// Repeated function applications, useful for big-step rotations/shifts

def apply0 f x { x };

def apply1 f x { f (apply0 f x) };

def apply2 f x { f (apply1 f x) };

def apply3 f x { f (apply2 f x) };

def apply4 f x { f (apply3 f x) };

def apply5 f x { f (apply4 f x) };

def apply6 f x { f (apply5 f x) };

def apply7 f x { f (apply6 f x) };

// Arithmetic shift right for 8 bit values

def ashr8 x {
    def (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7,ar)))))))) = range 8 x;
    combine8 (a1,(a2,(a3,(a4,(a5,(a6,(a7,(a7,()))))))))
};

// Logical shift right for 8 bit values

def lshr8 x {
    def (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7,ar)))))))) = range 8 x;
    combine8 (a1,(a2,(a3,(a4,(a5,(a6,(a7,(0,()))))))))
};

// Shift left for 8 bit values

def shl8 x {
    def (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7,ar)))))))) = range 8 x;
    combine8 (0,(a0,(a1,(a2,(a3,(a4,(a5,(a6,()))))))))
};

// Rotate right for 8 bit values

def ror8 x {
    def (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7,ar)))))))) = range 8 x;
    combine8 (a1,(a2,(a3,(a4,(a5,(a6,(a7,(a0,()))))))))
};

// Rotate left for 8 bit values

def rol8 x {
    def (a0,(a1,(a2,(a3,(a4,(a5,(a6,(a7,ar)))))))) = range 8 x;
    combine8 (a7,(a0,(a1,(a2,(a3,(a4,(a5,(a6,()))))))))
};

// Check the operations work correctly

242 = xor8 13 255;

254 = not8 1;
