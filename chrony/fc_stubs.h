#include <unistd.h>
#include "logging.h"

volatile int __fc_fs;

/*@
  requires valid_read_string(path);
  assigns \result, __fc_fs \from __fc_fs, path[0..], owner, group;
*/
extern int chown(const char *path, uid_t owner, gid_t group);
