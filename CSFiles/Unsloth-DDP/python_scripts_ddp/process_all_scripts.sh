#!/bin/bash
# Batch script to fetch all Python scripts from GitHub and convert them to DDP versions
# This script should be run from the python_scripts_ddp directory

set -e  # Exit on error

REPO="hnxnq7/Unsloth_notebooks"
OUTPUT_DIR="ddp_output"
TEMP_DIR="temp_scripts"

echo "========================================================================"
echo "Batch Processing: Convert Unsloth Scripts to DDP-Ready Versions"
echo "========================================================================"
echo ""

# Check if convert_to_ddp.py exists
if [ ! -f "convert_to_ddp.py" ]; then
    echo "❌ Error: convert_to_ddp.py not found in current directory"
    echo "   Please run this script from the python_scripts_ddp directory"
    exit 1
fi

# Check if requests library is installed (optional but recommended)
python3 -c "import requests" 2>/dev/null || {
    echo "⚠ Warning: requests library not found. Installing..."
    pip install requests || {
        echo "⚠ Could not install requests. Will try git clone fallback."
    }
}

echo "📥 Step 1: Fetching scripts from GitHub..."
echo "   Repository: $REPO/python_scripts"
echo "   Excluding: GRPO scripts"
echo ""

# Try to use the converter with GitHub option
python3 convert_to_ddp.py \
    --github "$REPO" \
    --output "$OUTPUT_DIR" \
    --exclude GRPO

if [ $? -eq 0 ]; then
    echo ""
    echo "✅ Successfully processed scripts from GitHub"
    echo ""
    echo "📁 Output directory: $OUTPUT_DIR"
    echo "📊 Processed scripts:"
    ls -1 "$OUTPUT_DIR"/*.py 2>/dev/null | wc -l | xargs echo "   Total:"
    echo ""
    echo "💡 Next steps:"
    echo "   1. Review the converted scripts in: $OUTPUT_DIR/"
    echo "   2. Upload to Kaggle"
    echo "   3. Run with: torchrun --nproc_per_node=2 <script_name>.py"
    exit 0
else
    echo ""
    echo "⚠ GitHub fetch failed. Trying alternative approach..."
    echo ""
    
    # Alternative: Clone repo manually and process
    if command -v git &> /dev/null; then
        echo "📥 Step 1b: Cloning repository..."
        CLONE_DIR="temp_repo"
        rm -rf "$CLONE_DIR"
        
        git clone --depth 1 "https://github.com/$REPO.git" "$CLONE_DIR" || {
            echo "❌ Git clone failed. Please ensure:"
            echo "   1. You have internet access"
            echo "   2. Git is installed"
            echo "   3. Repository URL is correct"
            exit 1
        }
        
        if [ ! -d "$CLONE_DIR/python_scripts" ]; then
            echo "❌ python_scripts directory not found in repository"
            exit 1
        fi
        
        echo "📝 Step 2: Converting scripts..."
        python3 convert_to_ddp.py \
            --input-dir "$CLONE_DIR/python_scripts" \
            --output "$OUTPUT_DIR" \
            --exclude GRPO
        
        echo ""
        echo "🧹 Cleaning up..."
        rm -rf "$CLONE_DIR"
        
        if [ -d "$OUTPUT_DIR" ] && [ "$(ls -A $OUTPUT_DIR/*.py 2>/dev/null)" ]; then
            echo ""
            echo "✅ Successfully converted scripts"
            echo "📁 Output directory: $OUTPUT_DIR"
            exit 0
        else
            echo "❌ No scripts were converted"
            exit 1
        fi
    else
        echo "❌ Git is not installed. Please install git or use manual file processing."
        echo ""
        echo "Alternative: Process local files manually:"
        echo "   python3 convert_to_ddp.py --input-dir /path/to/scripts --output $OUTPUT_DIR --exclude GRPO"
        exit 1
    fi
fi
