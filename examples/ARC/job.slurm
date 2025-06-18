#!/bin/bash

# ===================================================================
# SLURM Script for Parallel ARC Solver (Tailored for DIFCUL HPC)
# ===================================================================

# --- Resource Allocation (Adapted from your README) ---
#SBATCH --job-name=arc_solver
#SBATCH --partition=compute
#SBATCH --output=/mnt/storage/admindi/home/phsilva/slurm_outputs/%x_%a.out
#SBATCH --error=/mnt/storage/admindi/home/phsilva/slurm_outputs/%x_%a.err
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=00:10:00

# --- Job Array ---
#SBATCH --array=1-400

# --- Environment Setup ---
echo "Setting up environment..."
module load anaconda3/2023.09
# IMPORTANT: Replace 'my_aeon_env' with the actual name of your conda environment if it's different.
source activate my_aeon_env

# --- Job Execution ---
# Get the specific task ID for this job instance from the task_list.txt file.
TASK_ID=$(sed -n "${SLURM_ARRAY_TASK_ID}p" task_list.txt)

echo "------------------------------------------------"
echo "SLURM JOB ID: $SLURM_JOB_ID"
echo "SLURM ARRAY TASK ID: $SLURM_ARRAY_TASK_ID"
echo "Assigned ARC Task ID: $TASK_ID"
echo "------------------------------------------------"

# Run the Python solver, logging results to a single CSV file
python arc_for_script.py --task_id "$TASK_ID" --csv_file "arc_results_$TASK_ID.csv"

echo "Job finished."
