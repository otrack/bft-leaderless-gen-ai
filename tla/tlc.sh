#!/bin/sh

TLCDIR=/home/otrack/Implementation/TLA/tlaplus/tlatools/org.lamport.tlatools

# java -cp ${TLCDIR}/dist/tla2tools.jar:${TLCDIR}/dist/CommunityModules-deps.jar tlc2.TLC DDS
# java -cp ${TLCDIR}/dist/tla2tools.jar:${TLCDIR}/dist/CommunityModules-deps.jar tlc2.TLC Machine
# java -cp ${TLCDIR}/dist/tla2tools.jar:${TLCDIR}/dist/CommunityModules-deps.jar tlc2.TLC BQS
java -cp ${TLCDIR}/dist/tla2tools.jar:${TLCDIR}/dist/CommunityModules-deps.jar tlc2.TLC -workers $(nproc) EPaxos

