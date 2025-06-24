import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import os
import glob
import argparse

def plot_results(csv_directory: str, output_directory: str):
    """
    Reads all CSV files from a directory, combines them, and generates
    a histogram of test fitness and a scatter plot of fitness vs. time.

    Args:
        csv_directory (str): The path to the directory containing the result CSVs.
        output_directory (str): The path to save the generated plot images.
    """
    # --- Load and Combine Data ---
    # Find all CSV files in the specified directory
    all_files = glob.glob(os.path.join(csv_directory, "*.csv"))
    
    if not all_files:
        print(f"Error: No CSV files found in directory '{csv_directory}'.")
        return

    # Read each CSV and append it to a list
    df_list = []
    for filename in all_files:
        try:
            df_list.append(pd.read_csv(filename))
        except pd.errors.EmptyDataError:
            print(f"Warning: Skipping empty or malformed file: {filename}")
            continue

    if not df_list:
        print("Error: All CSV files were empty or could not be read.")
        return
        
    # Concatenate all dataframes into one
    results_df = pd.concat(df_list, ignore_index=True)

    # Ensure data types are correct for plotting, using the corrected column name
    results_df['test_fitness'] = pd.to_numeric(results_df['test_fitness'], errors='coerce')
    results_df['time_taken'] = pd.to_numeric(results_df['time_taken'], errors='coerce')
    results_df.dropna(subset=['test_fitness', 'time_taken'], inplace=True)

    print(f"Successfully loaded {len(results_df)} results.")

    # --- Extract Metadata for Plot Titles ---
    dsl_version = results_df['dsl_version'].iloc[0] if 'dsl_version' in results_df.columns and not results_df.empty else 'N/A'
    algorithm_version = results_df['algorithm_version'].iloc[0] if 'algorithm_version' in results_df.columns and not results_df.empty else 'N/A'
    
    # --- Create Plots ---
    # Set a nice style for the plots
    sns.set_theme(style="whitegrid")
    
    # Ensure the output directory exists
    os.makedirs(output_directory, exist_ok=True)

    # --- Plot 1: Histogram of Test Fitness ---
    plt.figure(figsize=(12, 7))
    sns.histplot(data=results_df, x='test_fitness', bins=20, kde=False)
    
    
    title_str = (
        f'Distribution of Test Fitness Scores Across All Tasks\n'
        f'(DSL Version: {dsl_version} | Algorithm: {algorithm_version})'
    )
    plt.title(title_str, fontsize=16)
    
    plt.xlabel('Test Fitness Score', fontsize=12)
    plt.ylabel('Number of Tasks', fontsize=12)
    plt.xlim(0, 1) # Fitness score is between 0 and 1
    histogram_path = os.path.join(output_directory, "fitness_histogram.png")
    plt.savefig(histogram_path, dpi=300, bbox_inches='tight')
    print(f"Saved fitness histogram to: {histogram_path}")
    plt.close()

    # --- Plot 2: Fitness vs. Running Time ---
    plt.figure(figsize=(12, 7))
    
    sns.scatterplot(data=results_df, x='time_taken', y='test_fitness', alpha=0.6)
    
    # Create an informative title with the new metadata
    title_str_scatter = (
        f'Test Fitness vs. Running Time\n'
        f'(DSL Version: {dsl_version} | Algorithm: {algorithm_version})'
    )
    plt.title(title_str_scatter, fontsize=16)

    plt.xlabel('Running Time (seconds)', fontsize=12)
    plt.ylabel('Test Fitness Score', fontsize=12)
    plt.ylim(-0.05, 1.05) # Give a little space around the 0-1 range
    plt.xscale('log') # Use a log scale for time if it varies greatly
    scatter_path = os.path.join(output_directory, "fitness_vs_time_scatter.png")
    plt.savefig(scatter_path, dpi=300, bbox_inches='tight')
    print(f"Saved fitness vs. time scatter plot to: {scatter_path}")
    plt.close()

if __name__ == '__main__':
    # --- Command-Line Argument Parsing ---
    parser = argparse.ArgumentParser(description="Plot results from ARC solver experiments.")
    
    parser.add_argument("--csv_dir", default="arc_results", type=str, help="Directory containing the individual CSV result files.")
    parser.add_argument("--output_dir", default="plots", type=str, help="Directory to save the plot images.")
    
    args = parser.parse_args()
    
    plot_results(args.csv_dir, args.output_dir)