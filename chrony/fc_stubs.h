#include <unistd.h>
#include "logging.h"

volatile int __fc_fs;

/*@
  requires valid_read_string(path);
  assigns \result, __fc_fs \from __fc_fs, path[0..], owner, group;
*/
extern int chown(const char *path, uid_t owner, gid_t group);

// skip verification of logging-related code
/*@
  assigns \nothing;
*/
void LOG_FileWrite(LOG_FileID id, const char *format, ...);

/*@
  requires valid_string(line);
  assigns line[0..strlen(\old(line))-1] \from line[0..strlen(\old(line))];
*/
void CPS_NormalizeLine(char *line);
