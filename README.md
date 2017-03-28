# logic
Attribute grammar for manipulating logical circuits

## Usage
This program is written in the Silver programming language.  Installation instructions can be found here, the latest development release is required: http://melt.cs.umn.edu/silver/doc/install-guide/
To compile the code, run the script `./compile.sh`.  This will build a jarfile `logic.jar`.
To run the code, run `java -jar logic.jar <filename>.circuit`.  This will print the logic expressions corresponding to all pairs of terminals, and generate a dotfile `out.dot`.  This can be viewed with many free programs, such as `xdot`, or rendered to several image formats with the standard utility `dot`.  