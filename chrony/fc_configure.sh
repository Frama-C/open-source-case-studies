# configuration to disable optional modules
# NOTE: you also need to manually remove some entries from the generated
#       configure:
# - comment out this line: add_def HAVE_IN_PKTINFO
# - comment out this line: add_def HAVE_RECVMMSG
# - comment out this line: add_def _GNU_SOURCE
# - comment out this line: add_def HAVE_RECVMMSG

CPPFLAGS="-nostdlib" \
      ./configure --disable-ipv6 --disable-timestamping --disable-readline
