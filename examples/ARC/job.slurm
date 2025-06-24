#!/bin/bash

# ===================================================================
# SLURM Script for Parallel ARC Solver
# ===================================================================

# --- Resource Allocation ---
#SBATCH --job-name=arc_solver
#SBATCH --partition=compute
#SBATCH --output=/mnt/storage/admindi/home/phsilva/slurm_outputs/%x_%a.out
#SBATCH --error=/mnt/storage/admindi/home/phsilva/slurm_outputs/%x_%a.err
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=12:00:00

# --- Job Array ---
#SBATCH --array=1-400

export PYTHONPATH=/mnt/storage/admindi/home/phsilva/aeon:$PYTHONPATH
echo "PYTHONPATH set to: $PYTHONPATH"

# --- Job Execution ---
# Get the specific task ID for this job instance from the task_list.txt file.
TASK_ID=$(sed -n "${SLURM_ARRAY_TASK_ID}p" task_list.txt)

echo "------------------------------------------------"
echo "SLURM JOB ID: $SLURM_JOB_ID"
echo "SLURM ARRAY TASK ID: $SLURM_ARRAY_TASK_ID"
echo "Assigned ARC Task ID: $TASK_ID"
echo "------------------------------------------------"

# Run the Python solver
python arc_for_script.py --task_id "$TASK_ID" --output_dir "arc_results"

echo "Job finished."
