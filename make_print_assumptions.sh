#!/bin/bash

#################################################
#                                               #                    
#      Functions to help the main script        #
#                                               #
#################################################
print_warning() {
  echo -e "\e[1;33mWarning:  $1\e[0m" >&2
}

strip_comments() {
  local depth=0
  local i=0
  local line
  local output=""

  while IFS='' read -r line || [ -n "$line" ]; do
    i=0
    while [ $i -lt ${#line} ]; do
      # If we're inside a comment, keep scanning until we find '*)'
      if [ $depth -gt 0 ]; then
        if [ "${line:$i:2}" = "*)" ]; then
          depth=$((depth - 1))
          i=$((i + 2))
        else
          i=$((i + 1))
        fi
      else
        # We're outside of a comment; look for start of comment '(*'
        if [ "${line:$i:2}" = "(*" ]; then
          depth=$((depth + 1))
          i=$((i + 2))
        else
          # This character is not part of a comment, so output it
          output+="${line:$i:1}"
          i=$((i + 1))
        fi
      fi
    done

    # If we're still in depth>0, that means the comment continues on the next line
    # so we do NOT print a newline if we are inside a comment.
    if [ $depth -eq 0 ]; then
      echo "$output"
      output=""
    fi
  done

  # If the file ended but we are still in a comment (depth > 0),
  # we simply never print those final lines, as they are part of the comment.
  if [ $depth -gt 0 ]; then
    print_warning "strip_comments(): The input ended with an open comment."
  fi
}

#################################################
#                                               #
#      Main script to extract assumptions       #
#                                               #
#################################################
# Input: Coq source file (e.g., MyFile.v)
COQFILE=$1
COQDIR=$2
OUTPUT=$3

# Step 1: Extract module names and their contexts
module_stack=() # Stack to manage multi-level modules
temp_theorems=$(mktemp) # Clear the temporary file
current_theorem=""
theorem_open=false

if [ ! -f "$COQFILE" ]; then
  echo "File not found: $COQFILE" >&2
  exit 1
fi

strip_comments < "$COQFILE" | while IFS= read -r line; do
  if echo "$line" | grep -qE "^[ \t]*Module "; then
    # Push module name onto the stack
    module_name=$(echo "$line" | sed -E 's/^[ \t]*Module +([^ ]+).*/\1/')
    module_stack+=("$module_name")
  elif echo "$line" | grep -qE "^[ \t]*End "; then
    # Pop module name from the stack
    if [ ${#module_stack[@]} -gt 0 ]; then
      unset 'module_stack[-1]'
    else
      print_warning "'End' encountered without matching 'Module'."
    fi
  elif echo "$line" | grep -qE "^[ \t]*(Theorem|Lemma|Example)"; then
    if $theorem_open; then
      print_warning "Theorem/lemma/example not closed properly: '$current_theorem'."
    fi
    # Extract theorem/lemma/example name
    current_theorem=$(echo "$line" | sed -E 's/^[ \t]*(Theorem|Lemma|Example) +([^ :]+).*/\2/')
    theorem_open=true
  elif $theorem_open && (echo "$line" | grep -qE "^.*[ \t]+(Qed|Admitted)[.][ \t]*$|^(Qed|Admitted)[.][ \t]*$"); then
    # If Qed. is found, finalize the theorem
    qualified_name=$(IFS=""; echo "${module_stack[*]}$current_theorem")
    qualified_name=${qualified_name#.} # Remove leading dot if no module
    echo "$qualified_name" >> "$temp_theorems"
    theorem_open=false
  fi
done

# Check if the last theorem/lemma was not closed
if $theorem_open; then
  print_warning "File ended with an open theorem/lemma/example '$current_theorem' not closed by Qed."
fi

# Step 2: Create a Coq script with Print Assumptions
echo "(* Generated script to check assumptions *)" > "$OUTPUT"
echo "From Coq Require Import String." >> "$OUTPUT"
echo "From $COQDIR Require Import ${1/.v/}." >> "$OUTPUT"
echo "Set Printing Width 100." >> "$OUTPUT"
echo "Ltac PT A :=" >> "$OUTPUT"
echo "   idtac \"-----------\" A \"-----------\"." >> "$OUTPUT"
echo "Goal True." >> "$OUTPUT"
while read -r theorem; do
  echo "first [ PT $theorem | PT @$theorem ]." >> "$OUTPUT"
  echo "Print Assumptions $theorem." >> "$OUTPUT"
done < "$temp_theorems"
echo "Abort." >> "$OUTPUT"

# Step 3: Remove the temporary file
# rm -f -- "$temp_theorems"
