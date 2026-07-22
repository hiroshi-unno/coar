#!/bin/bash
#
# This script finds all shared library dependencies for a given executable,
# identifies their source packages, and copies both the library and its
# license file to destination directories.
#

# --- Fail fast on any error ---
set -euo pipefail
IFS=$'\n\t'

# --- Function to get package name for a given library ---
get_package_name() {
    local lib_path="$1"

    # Check if the library file exists
    if [ ! -f "$lib_path" ]; then
        echo " -> WARNING: Library file does not exist. Skipping."
        return 1
    fi

    # These will be set as global variables on success
    package_name=""

    # Find the package that owns the file
    # Suppress exit-on-error for this line.
    package_name=$(dpkg -S "$lib_path" | cut -d':' -f1 || true)
    if [ -z "$package_name" ]; then
        echo " -> WARNING: Could not find an apt package. Skipping."
        return 1 # Signal failure
    fi
}

# --- Function to get license file for a given package name ---
get_package_license() {
    local package_name="$1"

    # Find the corresponding copyright file
    copyright_file="/usr/share/doc/$package_name/copyright"
    if [ ! -f "$copyright_file" ]; then
        echo " -> WARNING: Could not find copyright file for '$package_name'. Skipping."
        return 1 # Signal failure
    fi

    return 0 # Signal success
}

# --- Add dependencies of given binary to $libraries_to_process
add_new_deps() {
    local binary_path="$1"

    local new_deps=$(ldd "$binary_path" | grep "=>" | awk '{print $3}')
    for new_lib in ${new_deps[@]}; do
        real_new_path=$(readlink -f "$new_lib")

        # Only add it to the to-do list if we haven't already processed it.
        if [[ ! -v processed_libraries["$real_new_path"] ]]; then
            libraries_to_process+=("$new_lib")
        fi
    done

    return 0
}

# --- Configuration ---
SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
PROJECT_ROOT=$(cd "$SCRIPT_DIR/.." && pwd)
DEST_LIB_DIR="${PROJECT_ROOT}/lib"
DEST_LICENSE_DIR="${PROJECT_ROOT}/THIRD_PARTY_LICENSE"

# --- Function to Print Usage and Exit ---
print_usage() {
    echo "This script finds all shared library dependencies for a given executable, 
identifies their source packages, and copies both the library and its 
license file to destination directories.

Usage: $0 [--output=<path/to/output-file>] <path/to/executable>" >&2
}

# --- Argument Parsing ---
OUTPUT_FILE=""
declare -a TARGET_BINARIES

while (( $# > 0 )); do
    case "$1" in
        --output* )
            OUTPUT_FILE="${1#--output=}"
            shift
            ;;
        --help )
            print_usage
            exit
            ;;
        -* )
            echo "Error: Unknown option: $1" >&2
            print_usage
            exit 1
            ;;
        * )
            # Assume this is the target binary path
            TARGET_BINARIES+=("$1")
            shift
            ;;
    esac
done

# --- Validation ---
if (( ${#TARGET_BINARIES[@]} == 0 )); then
    echo "Error: No target binary specified." >&2
    print_usage
    exit 1
fi

# --- Main Logic ---
echo "Starting dependency and license gathering"

# Declare an associative array to track processed packages,
# which avoids copying the same license file multiple times.
declare -A processed_packages
declare -A processed_libraries

declare -a libraries_to_process
for binary_path in ${TARGET_BINARIES[@]}; do
    if [ ! -f "$binary_path" ]; then
        echo "Error: Target file not found at '$binary_path'" >&2
        exit 1
    fi

    echo "processing $binary_path"
    add_new_deps $binary_path
done

while (( "${#libraries_to_process[@]}" > 0 )); do
    lib_path=${libraries_to_process[-1]}
    unset 'libraries_to_process[-1]'

    echo "--------------------------------------------------"
    echo "Processing dependency: $lib_path"

    real_path=$(readlink -f "$lib_path")

    if [[ -v processed_libraries[$real_path] ]]; then
        echo " -> INFO: Shared librariy '$real_path' already processed. Skipping."
        continue
    fi

    if ! get_package_name "$real_path"; then
        continue
    fi

    echo " -> Found in package: $package_name"

    lib_filename=$(basename "$lib_path")
    if [ -n "$OUTPUT_FILE" ]; then
        echo "- ${lib_filename}: ${package_name}.license" >> $OUTPUT_FILE
    fi

    # If we haven't copied license file for this package yet,
    # seek and copy it.
    if [[ -v processed_packages[$package_name] ]]; then
        echo " -> INFO: License file for package '$package_name' already processed. Skipping."
    elif get_package_license "$package_name"; then
        echo " -> Copying copyright file at: $copyright_file"
        cp "$copyright_file" "$DEST_LICENSE_DIR/$package_name.license"

        add_new_deps $lib_path

        # Mark this package as processed
        processed_packages[$package_name]=1
    else
        continue
    fi

    # If we reached here, both package name and license file were found. Copy library.
    echo " -> SUCCESS: Copying library."
    cp "$lib_path" "$DEST_LIB_DIR/"
    chmod 755 "${DEST_LIB_DIR}/${lib_filename}"

    processed_libraries[$real_path]=1
done

echo "--------------------------------------------------"
echo "Process complete. Files are in '$DEST_LIB_DIR' and '$DEST_LICENSE_DIR'."

if [ -n "$OUTPUT_FILE" ]; then
    echo "Library path and license files are logged in '$OUTPUT_FILE' ."
fi