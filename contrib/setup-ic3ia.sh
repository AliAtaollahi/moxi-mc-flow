#!/bin/bash
# Builds horn2vmt, the CHC front end that `translate.py <file>.smt2` calls.
#
# horn2vmt is part of ic3ia (Alberto Griggio, FBK, GPLv3) and links against
# MathSAT, whose licence requires accepting terms on a download page. Neither
# can be fetched unattended, so this script builds from a copy you already
# have:
#
#     IC3IA_DIR=/path/to/ic3ia MATHSAT_DIR=/path/to/mathsat ./contrib/setup-ic3ia.sh
#
# MathSAT is downloaded automatically if MATHSAT_DIR is unset. ic3ia is not:
# get it from https://es.fbk.eu/tools/ic3ia and point IC3IA_DIR at it.
source "$(dirname $0)/setup-utils.sh"

MATHSAT_VERSION=${MATHSAT_VERSION:-5.6.10}
MATHSAT_ARCHIVE=mathsat-$MATHSAT_VERSION-linux-x86_64

DEPS_DIR=$(cd $DEPS_DIR && pwd)

if [[ -z "$IC3IA_DIR" ]]; then
    echo "Set IC3IA_DIR to an ic3ia source tree"
    echo "  https://es.fbk.eu/tools/ic3ia"
    exit 1
fi

IC3IA_DIR=$(cd $IC3IA_DIR && pwd)

if [[ ! -f "$IC3IA_DIR/horn2vmt.cpp" ]]; then
    echo "$IC3IA_DIR does not look like an ic3ia source tree"
    exit 1
fi

if [[ -z "$MATHSAT_DIR" ]]; then
    pushd $DEPS_DIR
    curl -L -o $MATHSAT_ARCHIVE.tar.gz \
        "https://mathsat.fbk.eu/download.php?file=$MATHSAT_ARCHIVE.tar.gz"
    tar -xf $MATHSAT_ARCHIVE.tar.gz
    popd
    MATHSAT_DIR=$DEPS_DIR/$MATHSAT_ARCHIVE
fi

MATHSAT_DIR=$(cd $MATHSAT_DIR && pwd)

if [[ ! -f "$MATHSAT_DIR/lib/libmathsat.a" ]]; then
    echo "MathSAT not found in $MATHSAT_DIR"
    echo "  https://mathsat.fbk.eu"
    exit 1
fi

mkdir -p $IC3IA_DIR/build
pushd $IC3IA_DIR/build

cmake .. -DMATHSAT_DIR=$MATHSAT_DIR -DCMAKE_BUILD_TYPE=Release
make horn2vmt

if [[ $? -ne 0 ]]; then
    echo "Failed building horn2vmt"
    exit 1
fi

cp horn2vmt $DEPS_DIR/
popd
