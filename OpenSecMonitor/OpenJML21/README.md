# OpenJMLSecurity

This is a fork of the OpenJML tool with additions for run-time security.

## OpenJML Additions
Additions to source files outside of "uk.re.ac.openjmlsec" are marked with the header `//ADD-OPENJMLSEC` and footer `//ADD-END` for easy searching and replacement

Only the module jdk.compiler has been edited with the OpenJML-master repo.


# Project set up

The root of the project setup should have the projects:
- OpenJML-master
- Specs
- JMLAnnotations
- openjml.github.io
- Solvers

Each of these repos can be pulled / downloaded from [OpenJML's github](https://github.com/OpenJML)

Please make sure all versions of each repos are for OpenJML version "21-0.8" as that is the current version our tool runs upon.
The tool can be upgraded by copying all additions to the newer version, however due to OpenJML updating, I can not say if the additions will be stable in later releases.

This project is located in OpenJML-master/OpenJML21 (and where all commands should be ran in)

# Running

Currently, running the project in eclipse does not work due to using edited system library calls.
Instead, the command line is used to run classes.

## Building OpenJML
The building process is the same as OpenJml, see [building OpenJML](https://github.com/OpenJML/OpenJML/wiki/Building-OpenJML) for the process on that.
Building OpenJML is required to run JML4SEC and the generated class (any any-time changes are made to classes)

## Running files
The command `./openjml-run` is used to run this file.
The command line arguments for running in the development environment Specs can be passed by `-Dopenjml.eclipseSpecsProjectLocation=` `/PATH/TO/PROJECT/Specs`

The parameters for our tool are:
- `-DOpenJMLSec_LogFile=` the location to a file for OpenJML output to be put into at run-time, default is null and outputs to STDERR.
- `-OpenJMLSec_SourceFolder=` the location to the source folder of the project, default is "./".
- `-OpenJMLSec_openjml=` the location to the openjml bash script, default is "openjml".

Class path arguments are `-classpath /PATH/TO/PROJECT/OpenJML-master/OpenJML21/bin:/PATH/TO/PROJECT/OpenJML-master/OpenJML21/gson-2.8.1.jar`

### Running JML4SEC.java
Pass a valid path to a file and an output folder as two command line arguments:  `uk.gre.ac.openjmlsec.JML4Sec FILENAME.java OUTPUT_FOLDER`

### JML4SEC test script
An automated script for testing "JML4SEC" can be used to build and run the file.
It takes the name of the file (without .java ext): `./JML4SEC FILENAME`

### GEN test script
An automated script for testing "GEN" can be used to build and run a generated file from JML4SEC file.
It takes the name of the file (without .java ext): `./GEN FILENAME`

*note: both test scripts are dependent on how the project was set up, so they may not work if you edit the project set up*

