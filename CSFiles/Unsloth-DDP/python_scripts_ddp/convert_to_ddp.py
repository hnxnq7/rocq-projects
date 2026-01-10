#!/usr/bin/env python3
"""
Convert Unsloth Python scripts to DDP-ready versions with torchrun support.

This script:
1. Fetches Python scripts from GitHub repo (or processes local files)
2. Adds DDP initialization (torch.distributed)
3. Adds proper device handling (local_rank)
4. Adds compatibility fixes for PEFT and multi-GPU
5. Outputs DDP-ready scripts that can be run with: torchrun --nproc_per_node=2 script.py
"""

import os
import sys
import re
import argparse
from pathlib import Path
import subprocess
import tempfile
import shutil

# Try to import requests for GitHub API, but make it optional
try:
    import requests
    HAS_REQUESTS = True
except ImportError:
    HAS_REQUESTS = False
    print("⚠ Warning: requests library not found. Will only process local files.")


def fetch_github_files(repo_path, output_dir, exclude_patterns=None):
    """
    Fetch Python files from GitHub repo.
    
    Args:
        repo_path: GitHub repo path like "hnxnq7/Unsloth_notebooks"
        output_dir: Directory to save fetched files
        exclude_patterns: List of patterns to exclude (e.g., ["GRPO"])
    """
    if not HAS_REQUESTS:
        print("❌ Cannot fetch from GitHub without requests library.")
        print("   Install with: pip install requests")
        return []
    
    exclude_patterns = exclude_patterns or []
    exclude_patterns = [p.upper() for p in exclude_patterns]  # Case-insensitive
    
    # GitHub API URL
    api_url = f"https://api.github.com/repos/{repo_path}/contents/python_scripts"
    
    try:
        response = requests.get(api_url, timeout=10)
        response.raise_for_status()
        files = response.json()
    except Exception as e:
        print(f"❌ Failed to fetch from GitHub: {e}")
        print("   Trying git clone approach...")
        return fetch_via_git_clone(repo_path, output_dir, exclude_patterns)
    
    # Filter Python files and exclude GRPO
    python_files = []
    os.makedirs(output_dir, exist_ok=True)
    
    for item in files:
        if item['type'] == 'file' and item['name'].endswith('.py'):
            filename = item['name'].upper()
            # Check if should be excluded
            if any(pattern in filename for pattern in exclude_patterns):
                print(f"  ⏭ Skipping {item['name']} (excluded: {exclude_patterns})")
                continue
            
            # Download file
            try:
                file_response = requests.get(item['download_url'], timeout=10)
                file_response.raise_for_status()
                
                file_path = os.path.join(output_dir, item['name'])
                with open(file_path, 'wb') as f:
                    f.write(file_response.content)
                
                python_files.append(file_path)
                print(f"  ✓ Fetched: {item['name']}")
            except Exception as e:
                print(f"  ❌ Failed to download {item['name']}: {e}")
    
    return python_files


def fetch_via_git_clone(repo_path, output_dir, exclude_patterns):
    """Fallback: Try to clone repo and extract files"""
    print("  Trying git clone...")
    temp_dir = tempfile.mkdtemp()
    repo_url = f"https://github.com/{repo_path}.git"
    
    try:
        # Clone repo
        subprocess.run(
            ['git', 'clone', '--depth', '1', repo_url, temp_dir],
            check=True,
            capture_output=True,
            timeout=60
        )
        
        # Find Python files
        scripts_dir = os.path.join(temp_dir, 'python_scripts')
        if not os.path.exists(scripts_dir):
            print(f"  ❌ python_scripts directory not found in repo")
            return []
        
        python_files = []
        exclude_patterns = [p.upper() for p in exclude_patterns]
        
        for filename in os.listdir(scripts_dir):
            if filename.endswith('.py'):
                filename_upper = filename.upper()
                if any(pattern in filename_upper for pattern in exclude_patterns):
                    print(f"  ⏭ Skipping {filename} (excluded)")
                    continue
                
                src = os.path.join(scripts_dir, filename)
                dst = os.path.join(output_dir, filename)
                shutil.copy2(src, dst)
                python_files.append(dst)
                print(f"  ✓ Copied: {filename}")
        
        # Cleanup
        shutil.rmtree(temp_dir)
        return python_files
    
    except Exception as e:
        print(f"  ❌ Git clone failed: {e}")
        if os.path.exists(temp_dir):
            shutil.rmtree(temp_dir)
        return []


def add_ddp_initialization(script_content):
    """Add DDP initialization code at the beginning of the script"""
    
    # Check if DDP initialization already exists
    if 'def setup_ddp()' in script_content or 'torch.distributed.init_process_group' in script_content:
        return None  # Already has DDP setup
    
    ddp_init = '''# ============================================================================
# DDP INITIALIZATION (MUST BE FIRST, BEFORE MODEL LOADING)
# ============================================================================
import os
import torch
import torch.distributed as dist
from torch.nn.parallel import DistributedDataParallel as DDP

def setup_ddp():
    """Initialize distributed training environment"""
    rank = int(os.environ.get("RANK", -1))
    local_rank = int(os.environ.get("LOCAL_RANK", -1))
    world_size = int(os.environ.get("WORLD_SIZE", -1))
    
    if rank == -1:
        # Not running with torchrun - single process mode
        print("⚠️  Not running with DDP. Use: torchrun --nproc_per_node=2 script.py")
        print("   Falling back to single GPU or DataParallel mode...")
        return None, None, None
    
    # Set device for this process
    torch.cuda.set_device(local_rank)
    
    # Initialize process group
    dist.init_process_group(backend="nccl")
    
    # Print DDP info (only from rank 0)
    if rank == 0:
        print(f"✅ DDP initialized: RANK={rank}, LOCAL_RANK={local_rank}, WORLD_SIZE={world_size}")
        print(f"   Process 0 using GPU {local_rank}: {torch.cuda.get_device_name(local_rank)}")
        if world_size > 1:
            print(f"   Process 1 will use GPU {1 if local_rank == 0 else 0}")
    
    return rank, local_rank, world_size

# Initialize DDP before anything else
rank, local_rank, world_size = setup_ddp()
is_main_process = rank == 0 if rank is not None else True

'''
    
    # Find where to insert (after shebang and docstring, before imports)
    lines = script_content.split('\n')
    insert_idx = 0
    
    # Skip shebang
    if lines and lines[0].startswith('#!'):
        insert_idx = 1
    
    # Skip docstring
    if insert_idx < len(lines) and '"""' in lines[insert_idx]:
        # Find end of docstring
        insert_idx += 1
        in_docstring = True
        while insert_idx < len(lines) and in_docstring:
            if '"""' in lines[insert_idx]:
                in_docstring = False
            insert_idx += 1
    
    # Skip empty lines
    while insert_idx < len(lines) and not lines[insert_idx].strip():
        insert_idx += 1
    
    # Check if os and torch imports exist - insert before them
    for i in range(insert_idx, min(insert_idx + 10, len(lines))):
        if lines[i].strip().startswith('import os') or lines[i].strip().startswith('import torch'):
            insert_idx = i
            break
    
    # Insert DDP initialization
    new_lines = lines[:insert_idx] + [''] + ddp_init.split('\n') + lines[insert_idx:]
    
    return '\n'.join(new_lines)


def add_compatibility_fixes(script_content):
    """Add compatibility fixes for PEFT and multi-GPU"""
    
    # Check if fixes already exist
    if 'COMPATIBILITY FIXES FOR PEFT' in script_content:
        return None  # Already has fixes
    
    fixes = '''
# ============================================================================
# COMPATIBILITY FIXES FOR PEFT LIBRARY AND MULTI-GPU
# ============================================================================
# These fixes ensure compatibility with PEFT library and multi-GPU attention mechanisms
# Only needed when running with DDP

if rank is not None and torch.cuda.device_count() > 1:
    import inspect
    try:
        from peft import LoraConfig
        
        # Fix 1: Patch LoraConfig for ensure_weight_tying compatibility
        sig = inspect.signature(LoraConfig.__init__)
        has_ensure_weight_tying = 'ensure_weight_tying' in sig.parameters
        
        if not has_ensure_weight_tying:
            original_init = LoraConfig.__init__
            def patched_init(self, *args, **kwargs):
                kwargs.pop('ensure_weight_tying', None)
                return original_init(self, *args, **kwargs)
            LoraConfig.__init__ = patched_init
            if is_main_process:
                print("✓ Patched LoraConfig for ensure_weight_tying compatibility")
        
        # Fix 2: Patch attention mechanism for multi-GPU device placement
        try:
            from xformers.ops.fmha.common import Inputs
            from xformers.ops.fmha import _memory_efficient_attention_forward
            
            original_validate = Inputs.validate_inputs
            def patched_validate_inputs(self):
                if self.attn_bias is not None:
                    query_device = self.query.device
                    if hasattr(self.attn_bias, 'q_seqinfo'):
                        if hasattr(self.attn_bias.q_seqinfo, 'seqstart'):
                            if self.attn_bias.q_seqinfo.seqstart.device != query_device:
                                self.attn_bias.q_seqinfo.seqstart = \\
                                    self.attn_bias.q_seqinfo.seqstart.to(query_device)
                return original_validate(self)
            Inputs.validate_inputs = patched_validate_inputs
            
            original_forward = _memory_efficient_attention_forward
            def patched_forward(inp, op=None):
                if inp.attn_bias is not None and inp.query is not None:
                    query_device = inp.query.device
                    if hasattr(inp.attn_bias, 'q_seqinfo'):
                        if hasattr(inp.attn_bias.q_seqinfo, 'seqstart'):
                            if inp.attn_bias.q_seqinfo.seqstart.device != query_device:
                                inp.attn_bias.q_seqinfo.seqstart = \\
                                    inp.attn_bias.q_seqinfo.seqstart.to(query_device)
                return original_forward(inp, op)
            
            import xformers.ops.fmha
            xformers.ops.fmha._memory_efficient_attention_forward = patched_forward
            if is_main_process:
                print("✓ Patched attention mechanism for multi-GPU compatibility")
        except Exception as e:
            if is_main_process:
                print(f"⚠ Could not patch attention mechanism: {e}")
    except Exception as e:
        if is_main_process:
            print(f"⚠ Could not apply compatibility fixes: {e}")

'''
    
    # Find where to insert (after DDP init, before model loading)
    lines = script_content.split('\n')
    insert_idx = len(lines)
    
    # Look for model loading line
    for i, line in enumerate(lines):
        if 'FastLanguageModel.from_pretrained' in line or 'FastVisionModel.from_pretrained' in line:
            insert_idx = i
            break
    
    # Insert before model loading
    new_lines = lines[:insert_idx] + fixes.split('\n') + lines[insert_idx:]
    
    return '\n'.join(new_lines)


def fix_device_handling(script_content):
    """Fix device handling to use local_rank in DDP mode"""
    
    # Replace hardcoded "cuda" or "cuda:0" with proper device handling
    # This is tricky - we need to be careful not to break things
    
    # Pattern 1: .to("cuda") -> .to(f"cuda:{local_rank if local_rank is not None else 0}")
    # Pattern 2: .to("cuda:0") -> .to(f"cuda:{local_rank if local_rank is not None else 0}")
    
    # Add device helper function
    device_helper = '''
# ============================================================================
# DEVICE HELPER FOR DDP
# ============================================================================
def get_device():
    """Get the appropriate device for this process"""
    if local_rank is not None:
        return f"cuda:{local_rank}"
    elif torch.cuda.is_available():
        return "cuda:0"
    else:
        return "cpu"

device = get_device()
if is_main_process:
    print(f"📱 Using device: {device}")

'''
    
    # Insert device helper after DDP init
    if 'def get_device()' not in script_content:
        lines = script_content.split('\n')
        insert_idx = 0
        for i, line in enumerate(lines):
            if 'is_main_process =' in line:
                insert_idx = i + 1
                break
        
        new_lines = lines[:insert_idx] + device_helper.split('\n') + lines[insert_idx:]
        script_content = '\n'.join(new_lines)
    
    # Replace common patterns (but be conservative)
    # Replace .to("cuda") with .to(device) when safe
    patterns = [
        (r'\.to\("cuda:0"\)', r'.to(device)'),
        (r'\.to\("cuda"\)', r'.to(device)'),
    ]
    
    for pattern, replacement in patterns:
        # Only replace if not already using device variable
        if 'device =' in script_content:
            script_content = re.sub(pattern, replacement, script_content)
    
    return script_content


def add_ddp_cleanup(script_content):
    """Add DDP cleanup at the end of the script"""
    
    if 'dist.destroy_process_group' in script_content:
        return None  # Already has cleanup
    
    cleanup = '''
# ============================================================================
# DDP CLEANUP
# ============================================================================
if rank is not None:
    dist.destroy_process_group()
    if is_main_process:
        print("✅ DDP cleanup complete")
'''
    
    # Add at the end of the file (before any __main__ guard)
    lines = script_content.split('\n')
    
    # Find last non-empty, non-comment line before __main__ or EOF
    insert_idx = len(lines)
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() and not lines[i].strip().startswith('#'):
            if '__main__' in lines[i] or 'if __name__' in lines[i]:
                continue
            insert_idx = i + 1
            break
    
    # Insert cleanup
    new_lines = lines[:insert_idx] + [''] + cleanup.split('\n') + lines[insert_idx:]
    
    return '\n'.join(new_lines)


def update_trainer_config(script_content):
    """Update trainer configuration to support DDP"""
    
    # Check if trainer config already has DDP settings
    if 'ddp_find_unused_parameters' in script_content:
        return None  # Already configured
    
    # Look for SFTConfig or TrainingArguments
    if 'SFTConfig(' in script_content:
        # Add ddp_find_unused_parameters to SFTConfig
        pattern = r'(report_to\s*=\s*"[^"]+",?\s*#?\s*[^\n]*)'
        replacement = r'\1\n        ddp_find_unused_parameters = False,  # Set to False for better DDP performance'
        script_content = re.sub(pattern, replacement, script_content, flags=re.MULTILINE)
    
    return script_content


def update_docstring(script_content, script_name):
    """Update docstring to include torchrun command"""
    
    script_basename = os.path.basename(script_name)
    
    # Pattern for docstring
    docstring_pattern = r'("""[\s\S]*?""")'
    new_docstring = f'"""\nTraining script with DDP support: {script_basename}\n\nRun with DDP (multi-GPU):\n    torchrun --nproc_per_node=2 {script_basename}\n\nRun single GPU:\n    python {script_basename}\n"""'
    
    if '"""' in script_content:
        # Replace existing docstring
        script_content = re.sub(docstring_pattern, new_docstring, script_content, count=1)
    else:
        # Add docstring after shebang
        lines = script_content.split('\n')
        if lines[0].startswith('#!'):
            lines.insert(1, '')
            lines.insert(2, new_docstring)
        else:
            lines.insert(0, new_docstring)
        script_content = '\n'.join(lines)
    
    return script_content


def convert_script_to_ddp(input_file, output_file):
    """Convert a single script to DDP-ready version"""
    
    print(f"\n📝 Processing: {os.path.basename(input_file)}")
    
    # Read input file
    try:
        with open(input_file, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"  ❌ Failed to read file: {e}")
        return False
    
    # Apply transformations
    transformations = [
        ("Updating docstring", update_docstring, (output_file,)),
        ("Adding DDP initialization", add_ddp_initialization, ()),
        ("Adding compatibility fixes", add_compatibility_fixes, ()),
        ("Fixing device handling", fix_device_handling, ()),
        ("Updating trainer config", update_trainer_config, ()),
        ("Adding DDP cleanup", add_ddp_cleanup, ()),
    ]
    
    modified = False
    for name, func, args in transformations:
        try:
            result = func(content, *args) if args else func(content)
            if result is not None:
                content = result
                print(f"  ✓ {name}")
                modified = True
            else:
                print(f"  ⊘ {name} (already present or skipped)")
        except Exception as e:
            print(f"  ⚠ {name} failed: {e}")
    
    # Deduplicate imports (remove duplicates after DDP init)
    lines = content.split('\n')
    seen_imports = set()
    deduped_lines = []
    ddp_end_idx = 0
    
    # Find where DDP section ends (after device helper)
    for i, line in enumerate(lines):
        if 'is_main_process =' in line or 'device = get_device()' in line:
            ddp_end_idx = i + 1
            # Scan ahead to find the end of the device helper section
            for j in range(i + 1, min(i + 10, len(lines))):
                if lines[j].strip() and not lines[j].strip().startswith('#') and 'def get_device()' not in lines[j] and 'device =' not in lines[j]:
                    ddp_end_idx = j
                    break
            break
    
    # First pass: collect imports from DDP section into seen_imports
    for i, line in enumerate(lines):
        if i < ddp_end_idx:
            line_stripped = line.strip()
            if line_stripped.startswith('import ') or line_stripped.startswith('from '):
                import_key = re.sub(r'\s+#.*$', '', line_stripped).strip()
                seen_imports.add(import_key)
    
    # Second pass: keep DDP section, deduplicate rest
    for i, line in enumerate(lines):
        if i < ddp_end_idx:
            deduped_lines.append(line)
            continue
        
        # Check for duplicate imports
        line_stripped = line.strip()
        if line_stripped.startswith('import ') or line_stripped.startswith('from '):
            # Normalize import line (remove comments, extra spaces)
            import_key = re.sub(r'\s+#.*$', '', line_stripped).strip()
            if import_key not in seen_imports:
                seen_imports.add(import_key)
                deduped_lines.append(line)
            # else: skip duplicate import (already in DDP section)
        else:
            deduped_lines.append(line)
    
    # Check if os import exists (needed for DDP)
    if 'import os' not in '\n'.join(deduped_lines):
        # Add os import if missing
        for i, line in enumerate(deduped_lines):
            if line.strip().startswith('import ') or line.strip().startswith('from '):
                deduped_lines.insert(i, 'import os')
                print("  ✓ Added missing 'import os'")
                break
    
    content = '\n'.join(deduped_lines)
    
    # Write output file
    try:
        os.makedirs(os.path.dirname(output_file) or '.', exist_ok=True)
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(content)
        print(f"  ✅ Created DDP-ready script: {os.path.basename(output_file)}")
        return True
    except Exception as e:
        print(f"  ❌ Failed to write output file: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description='Convert Unsloth Python scripts to DDP-ready versions',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Fetch from GitHub and convert all (except GRPO)
  python convert_to_ddp.py --github hnxnq7/Unsloth_notebooks --output ddp_scripts

  # Convert local files
  python convert_to_ddp.py --input script1.py script2.py --output ddp_scripts

  # Exclude additional patterns
  python convert_to_ddp.py --github hnxnq7/Unsloth_notebooks --exclude GRPO TEST
        """
    )
    
    parser.add_argument('--github', type=str, metavar='REPO',
                       help='GitHub repo path (e.g., "hnxnq7/Unsloth_notebooks")')
    parser.add_argument('--input', nargs='+', metavar='FILE',
                       help='Local Python script files to convert')
    parser.add_argument('--output', type=str, default='ddp_scripts',
                       help='Output directory for DDP-ready scripts (default: ddp_scripts)')
    parser.add_argument('--exclude', nargs='+', default=['GRPO'],
                       help='Patterns to exclude from processing (default: GRPO)')
    parser.add_argument('--input-dir', type=str,
                       help='Directory containing input scripts (alternative to --input)')
    
    args = parser.parse_args()
    
    # Determine input files
    input_files = []
    
    if args.github:
        print(f"📥 Fetching scripts from GitHub: {args.github}/python_scripts")
        print(f"   Excluding patterns: {args.exclude}")
        temp_input_dir = os.path.join(args.output, '_temp_input')
        os.makedirs(temp_input_dir, exist_ok=True)
        
        input_files = fetch_github_files(args.github, temp_input_dir, args.exclude)
        
        if not input_files:
            print("❌ No files fetched. Please check:")
            print("   1. Repository path is correct")
            print("   2. python_scripts directory exists in repo")
            print("   3. Network connection is available")
            return 1
    
    elif args.input:
        input_files = [f for f in args.input if f.endswith('.py') and os.path.exists(f)]
        if not input_files:
            print("❌ No valid Python files found in input list")
            return 1
    
    elif args.input_dir:
        if not os.path.isdir(args.input_dir):
            print(f"❌ Input directory not found: {args.input_dir}")
            return 1
        
        exclude_patterns = [p.upper() for p in args.exclude]
        for filename in os.listdir(args.input_dir):
            if filename.endswith('.py'):
                filename_upper = filename.upper()
                if any(pattern in filename_upper for pattern in exclude_patterns):
                    print(f"  ⏭ Skipping {filename} (excluded)")
                    continue
                input_files.append(os.path.join(args.input_dir, filename))
        
        if not input_files:
            print(f"❌ No Python files found in {args.input_dir} (or all excluded)")
            return 1
    
    else:
        parser.print_help()
        print("\n❌ Error: Must specify --github, --input, or --input-dir")
        return 1
    
    if not input_files:
        print("❌ No files to process")
        return 1
    
    print(f"\n🚀 Converting {len(input_files)} script(s) to DDP-ready versions...")
    
    # Create output directory
    os.makedirs(args.output, exist_ok=True)
    
    # Process each file
    success_count = 0
    for input_file in input_files:
        filename = os.path.basename(input_file)
        output_file = os.path.join(args.output, filename)
        
        if convert_script_to_ddp(input_file, output_file):
            success_count += 1
    
    print(f"\n{'='*70}")
    print(f"✅ Successfully converted {success_count}/{len(input_files)} script(s)")
    print(f"📁 Output directory: {args.output}")
    print(f"\n💡 To run with DDP on Kaggle 2x T4:")
    print(f"   torchrun --nproc_per_node=2 <script_name>.py")
    print(f"{'='*70}")
    
    # Cleanup temp directory if created
    temp_input_dir = os.path.join(args.output, '_temp_input')
    if os.path.exists(temp_input_dir):
        shutil.rmtree(temp_input_dir)
    
    return 0 if success_count == len(input_files) else 1


if __name__ == '__main__':
    sys.exit(main())
