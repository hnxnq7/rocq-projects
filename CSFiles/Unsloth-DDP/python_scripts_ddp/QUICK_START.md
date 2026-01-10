# Quick Start Guide: Converting Unsloth Scripts to DDP

## What Was Created

This directory contains tools to automatically convert existing Unsloth Python training scripts from the [Unsloth_notebooks repository](https://github.com/hnxnq7/Unsloth_notebooks/tree/main/python_scripts) into DDP-ready versions that can run on Kaggle 2x T4 GPUs.

## Files in This Directory

- **`convert_to_ddp.py`** - Main converter script (can process from GitHub or local files)
- **`process_github_scripts.py`** - Simple wrapper to fetch and process all scripts from GitHub
- **`process_all_scripts.sh`** - Bash script alternative for batch processing
- **`README.md`** - Full documentation
- **`ddp_output/`** - Directory where converted scripts will be saved

## Quick Usage

### Option 1: Process All Scripts from GitHub (Recommended)

```bash
cd python_scripts_ddp
python3 process_github_scripts.py
```

This will:
1. Fetch all `.py` files from `hnxnq7/Unsloth_notebooks/python_scripts`
2. Skip files with "GRPO" in the name
3. Convert each script to DDP-ready version
4. Save to `ddp_output/` directory

### Option 2: Using the Bash Script

```bash
cd python_scripts_ddp
bash process_all_scripts.sh
```

### Option 3: Manual Processing (Custom Files)

```bash
cd python_scripts_ddp
python3 convert_to_ddp.py --input-dir /path/to/scripts --output ddp_output --exclude GRPO
```

Or for specific files:
```bash
python3 convert_to_ddp.py --input script1.py script2.py --output ddp_output
```

## Requirements

Install dependencies:
```bash
pip install requests  # For GitHub API access (optional - git clone fallback available)
```

## What Gets Converted

Each script is modified to include:

1. ✅ **DDP Initialization** - Proper `torch.distributed` setup
2. ✅ **Device Handling** - Uses `local_rank` for multi-GPU
3. ✅ **Compatibility Fixes** - PEFT and xformers patches
4. ✅ **Trainer Configuration** - DDP-optimized settings
5. ✅ **DDP Cleanup** - Proper process group destruction
6. ✅ **Updated Docstring** - Includes `torchrun` instructions

## Running Converted Scripts on Kaggle

After conversion, upload scripts from `ddp_output/` to Kaggle and run:

```python
# In a Kaggle notebook cell:
!torchrun --nproc_per_node=2 <script_name>.py
```

For single GPU testing:
```python
!python <script_name>.py
```

## Excluded Scripts

Scripts with "GRPO" in the filename are automatically excluded because:
- GRPO uses reinforcement learning training loops
- RL training has sequential dependencies incompatible with DDP
- Custom RL trainers may not support DDP properly

## Expected Output

After running the converter, you should see:

```
ddp_output/
├── train_llama.py          # DDP-ready version
├── train_gpt_oss.py        # DDP-ready version
├── train_gemma.py          # DDP-ready version
└── ...                     # Other converted scripts (excluding GRPO ones)
```

## Verification

To verify a converted script, check that it contains:
- `def setup_ddp()` function
- `import torch.distributed as dist`
- `torchrun --nproc_per_node=2` in the docstring
- DDP cleanup at the end

## Troubleshooting

**Issue**: "Failed to fetch from GitHub"
- **Solution**: Ensure you have internet access and the repository is public, or use `--input-dir` with local files

**Issue**: "No files fetched"
- **Solution**: Check that `python_scripts` directory exists in the repository

**Issue**: Scripts still use only one GPU
- **Solution**: Make sure you're running with `torchrun --nproc_per_node=2`, not plain `python`

## Example Workflow

```bash
# 1. Navigate to the converter directory
cd python_scripts_ddp

# 2. Run the converter (fetches from GitHub automatically)
python3 process_github_scripts.py

# 3. Check output
ls -la ddp_output/

# 4. Upload to Kaggle and run with DDP
# In Kaggle notebook:
!torchrun --nproc_per_node=2 ddp_output/train_llama.py
```

## Next Steps

1. ✅ Convert scripts using the converter
2. ✅ Upload converted scripts to Kaggle
3. ✅ Run with `torchrun --nproc_per_node=2` for true DDP
4. ✅ Monitor GPU utilization to verify both GPUs are being used

## Support

For issues or questions:
- Check `README.md` for detailed documentation
- Review the converted script output for any errors
- Ensure Kaggle environment has 2x T4 GPUs enabled
