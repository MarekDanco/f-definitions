#!/bin/bash
# Author:  mikolas
# Created on:  Wed Feb 18 11:15:07 AM CET 2026
# Copyright (C) 2026, Mikolas Janota
#
set -e

VENV_DIR=".venv"
SCRIPT="extract_abstract.py"

# Check input
if [ -z "$1" ]; then
    echo "Usage: ./setup_and_run.sh yourfile.tex"
    exit 1
fi

# Create venv if it doesn't exist
if [ ! -d "$VENV_DIR" ]; then
    echo "Creating virtual environment..."
    python3 -m venv "$VENV_DIR"
fi

# Activate venv
source "$VENV_DIR/bin/activate"

# Install dependency if not already installed
pip show pylatexenc > /dev/null 2>&1 || pip install pylatexenc

# Run the script
python "$SCRIPT" "$1"

deactivate
