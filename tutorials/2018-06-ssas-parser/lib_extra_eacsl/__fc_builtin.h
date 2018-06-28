#include "stddef.h"



/*@ requires valid_p: \valid(p + (0 .. l-1));
    assigns p[0 .. l-1] \from Frama_C_entropy_source;
    assigns Frama_C_entropy_source \from Frama_C_entropy_source;
    ensures initialization: \initialized(p + (0 .. l-1));
*/
extern void Frama_C_make_unknown(char *p, size_t l);
