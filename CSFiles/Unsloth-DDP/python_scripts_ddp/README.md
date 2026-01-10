# DDP Script Converter for Unsloth Notebooks

This directory contains tools to convert existing Unsloth Python training scripts to DDP (Distributed Data Parallel) ready versions that can be run with `torchrun` on Kaggle 2x T4 GPUs.

## Overview

The `convert_to_ddp.py` script:
- Fetches Python scripts from the [Unsloth_notebooks](https://github.com/hnxnq7/Unsloth_notebooks) repository
- Converts them to DDP-ready versions with proper initialization and cleanup
- Excludes GRPO scripts (which are not compatible with DDP)
- Outputs scripts ready for `torchrun --nproc_per_node=2` execution

## Usage

### Option 1: Fetch from GitHub and Convert

```bash
python convert_to_ddp.py --github hnxnq7/Unsloth_notebooks --output ddp_output
```

This will:
1. Fetch all `.py` files from `hnxnq7/Unsloth_notebooks/python_scripts`
2. Exclude files with "GRPO" in the name
3. Convert each script to DDP-ready version
4. Save to `ddp_output/` directory

### Option 2: Convert Local Files

```bash
python convert_to_ddp.py --input script1.py script2.py --output ddp_output
```

### Option 3: Convert from Local Directory

```bash
python convert_to_ddp.py --input-dir /path/to/python_scripts --output ddp_output
```

### Exclude Additional Patterns

```bash
python convert_to_ddp.py --github hnxnq7/Unsloth_notebooks --exclude GRPO TEST --output ddp_output
```

## What the Converter Does

The converter adds the following to each script:

1. **DDP Initialization**: Sets up `torch.distributed` environment variables
2. **Device Handling**: Properly handles `local_rank` for multi-GPU training
3. **Compatibility Fixes**: Patches for PEFT library and xformers attention mechanisms
4. **Trainer Configuration**: Adds `ddp_find_unused_parameters=False` for optimal performance
5. **DDP Cleanup**: Properly destroys process groups at the end
6. **Updated Docstring**: Includes `torchrun` command instructions

## Running DDP Scripts on Kaggle

After conversion, upload the DDP-ready scripts to Kaggle and run:

```bash
!torchrun --nproc_per_node=2 <script_name>.py
```

For single GPU:
```bash
!python <script_name>.py
```

## Requirements

```bash
pip install requests  # For GitHub API access (optional)
```

If `requests` is not installed, the script will try to use `git clone` as a fallback.

## Excluded Scripts

By default, scripts with "GRPO" in the filename are excluded because:
- GRPO (Group Relative Policy Optimization) uses RL training loops
- RL training has sequential dependencies that don't parallelize well with DDP
- Custom RL trainers may not support DDP properly

## Output Structure

```
ddp_output/
├── script1_ddp.py
├── script2_ddp.py
└── ...
```

Each output script:
- Maintains the original filename
- Is ready for `torchrun` execution
- Can still run in single-GPU mode (falls back gracefully)

## Example Output Script Structure

```python
#!/usr/bin/env python3
"""
Training script with DDP support: example.py

Run with DDP (multi-GPU):
    torchrun --nproc_per_node=2 example.py

Run single GPU:
    python example.py
"""

import os
import torch
import torch.distributed as dist

# DDP Initialization
def setup_ddp():
    # ... DDP setup code ...

# Compatibility Fixes
# ... PEFT and xformers patches ...

# Original script code
# ... model loading, training, etc. ...

# DDP Cleanup
if rank is not None:
    dist.destroy_process_group()
```

## Troubleshooting

**Issue**: Script fails to fetch from GitHub
- **Solution**: Install `requests` library or ensure git is available

**Issue**: Scripts fail with DDP errors
- **Solution**: Ensure you're running with `torchrun`, not plain `python`

**Issue**: Only one GPU is being used
- **Solution**: Check that you're using `torchrun --nproc_per_node=2` (2 for 2 GPUs)

## Notes

- The converter preserves all original script functionality
- Scripts are backward compatible (work in single-GPU mode too)
- All modifications are clearly marked with comments
- GRPO and other excluded patterns are skipped automatically
