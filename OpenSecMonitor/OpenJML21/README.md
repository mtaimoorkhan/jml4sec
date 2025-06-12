# OpenJMLSecurity

This is a fork of the OpenJML tool with additions for run-time security.

## OpenJML Additions
Additions to source files outside of "uk.re.ac.openjmlsec" are marked with the header `//ADD-OPENJMLSEC` and footer `//ADD-END` for easy searching and replacement

Only the project jdk.compiler has been editied.


# Project set up

The root of the project setup should have the projects:
- OpenJML-master
- Specs
- JMLAnnotations
- openjml.github.io
- Solvers
Each of these repos can be pulled / downloaded from [OpenJML's github](https://github.com/OpenJML)

This project is located in OpenJML-master/OpenJML21 (and where all commands should be ran in)

# Running

Currently, running the project in eclipse does not work due to using edited system library calls.
Instead, the command line is used to run classes.

## Edit `uk.gre.ac.openjmlsec.FilePaths`
In `uk.gre.ac.openjmlsec.FilePaths` there is a constant `PROJECT_PATH` that contains the absolute path to the project location.

## Building OpenJML
The building process is the same as OpenJml, see [building OpenJML](https://github.com/OpenJML/OpenJML/wiki/Building-OpenJML) for the process on that.
Building OpenJML is required to run JML4SEC and the generated class (any anytime changes are made to classes)

## Running files
The command `./openjml-run` is used to run this file.
The command line arguments for running in the development environment Specs can be passed by `-Dopenjml.eclipseSpecsProjectLocation=` `/PATH/TO/PROJECT/Specs`
Class path arguments are `-classpath /PATH/TO/PROJECT/OpenJML-master/OpenJML21/bin:/PATH/TO/PROJECT/OpenJML-master/OpenJML21/gson-2.8.1.jar`

### Running JML4SEC.java
Pass a file located in `uk.gre.ac.openjmlsec.FilePaths.FILE_SOURCE_PATH` as a single command line argument: `uk.gre.ac.openjmlsec.JML4Sec FILENAME.java `

### JML4SEC test script
An automated script for testing "JML4SEC" can be used to build and run the file.
It takes the name of the file (without .java ext): `./JML4SEC FILENAME`

### GEN test script
An automated script for testing "GEN" can be used to build and run a generated file from JML4SEC file.
It takes the name of the file (without .java ext): `./GEN FILENAME`

*note: both test scripts are dependent on how the project was set up, so they may not work if you edit the project set up*

