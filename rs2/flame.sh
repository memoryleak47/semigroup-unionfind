#!/bin/bash

RUSTFLAGS="-C force-frame-pointers=yes" cargo flamegraph --unit-test -- test_trivial_arith
firefox flamegraph.svg
