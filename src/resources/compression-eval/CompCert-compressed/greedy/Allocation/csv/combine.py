import os

def extract_section(filename):
    """Step (1): Extract the part under the second set of dashes."""
    extracted_lines = []
    start_extracting = False
    with open(filename, 'r') as file:
        for line in file:
            if '---------------------------' in line:
                if start_extracting:  # If we have already encountered the second dashed line, start extracting
                    break
                start_extracting = True
            elif start_extracting:  # Collect lines after the second dashed line
                extracted_lines.append(line.strip())
    return extracted_lines

def retain_third_column(extracted_lines):
    """Step (2): Retain only the third column of the data."""
    third_column_data = []
    for line in extracted_lines:
        columns = line.split(',')
        if len(columns) >= 3:
            third_column_data.append(columns[2].strip())
    return third_column_data

def combine_files(third_column_data_list):
    """Step (3): Combine the third column data from multiple files."""
    combined_lines = []
    for i in range(len(third_column_data_list[0])):
        combined_line = ', '.join(third_column_data[i] for third_column_data in third_column_data_list)
        combined_lines.append(combined_line)
    return combined_lines

def get_sort_key(filename):
    """Extract the sorting key from the first line of the file."""
    with open(filename, 'r') as file:
        for line in file:
            if line.strip():  # Skip empty lines
                columns = line.split(',')
                if len(columns) >= 3:
                    try:
                        return float(columns[2].strip())  # Return the value as a float for sorting
                    except ValueError:
                        pass  # Ignore lines that do not contain a valid number
    return float('inf')  # Use infinity as a default to handle files without a valid number

# Get the directory where the Python script resides
script_directory = os.path.dirname(os.path.abspath(__file__))

# Automatically find input files in the script directory (e.g., files with a .txt extension)
input_files = [f for f in os.listdir(script_directory) if f.endswith('.csv') and f.startswith('Allocation')]

# Sort the input files based on the number in the first line
input_files.sort(key=lambda f: get_sort_key(os.path.join(script_directory, f)))

# Step (1) and Step (2): Extract and process the data from each file
third_column_data_list = []
for file_name in input_files:
    file_path = os.path.join(script_directory, file_name)
    extracted_lines = extract_section(file_path)
    third_column_data = retain_third_column(extracted_lines)
    third_column_data_list.append(third_column_data)

# Step (3): Combine the data into one file
combined_lines = combine_files(third_column_data_list)

# Write the combined data to an output file named 'Allocation-combined.csv'
output_file = os.path.join(script_directory, 'combined-Allocation.csv')
with open(output_file, 'w') as file:
    for line in combined_lines:
        file.write(line + '\n')

print(f'Combined data has been saved to {output_file}')
