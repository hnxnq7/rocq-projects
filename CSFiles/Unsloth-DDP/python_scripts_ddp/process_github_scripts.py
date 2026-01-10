#!/usr/bin/env python3
"""
Main script to process all scripts from GitHub repository.
This script fetches all Python scripts from the Unsloth_notebooks repo
(excluding GRPO ones) and converts them to DDP-ready versions.

Usage:
    python process_github_scripts.py
"""

import os
import sys
import subprocess

# Add current directory to path so we can import convert_to_ddp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from convert_to_ddp import main as convert_main

def process_all_github_scripts():
    """Process all scripts from GitHub repository"""
    
    print("="*70)
    print("Unsloth Scripts to DDP Converter")
    print("="*70)
    print()
    print("This script will:")
    print("  1. Fetch all Python scripts from: hnxnq7/Unsloth_notebooks/python_scripts")
    print("  2. Exclude scripts with 'GRPO' in the name")
    print("  3. Convert each script to DDP-ready version")
    print("  4. Save outputs to: ddp_output/")
    print()
    print("="*70)
    print()
    
    # Set up arguments for convert_to_ddp.py
    sys.argv = [
        'convert_to_ddp.py',
        '--github', 'hnxnq7/Unsloth_notebooks',
        '--output', 'ddp_output',
        '--exclude', 'GRPO'
    ]
    
    # Run the converter
    return convert_main()

if __name__ == '__main__':
    exit_code = process_all_github_scripts()
    sys.exit(exit_code)
