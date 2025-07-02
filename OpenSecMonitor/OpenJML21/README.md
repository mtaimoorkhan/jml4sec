# OpenJMLSecurity

This is a fork of the OpenJML tool with additions for run-time security.

## OpenJML Additions
Additions to source files outside of "uk.gre.ac.openjmlsec" are marked with the header `//ADD-OPENJMLSEC` and footer `//ADD-END` for easy searching and replacement

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
Building OpenJML is required to run JML4SEC, you will also need to make a release.
You then can use this release copy (located in "release-temp") to run our tool.

## Generating files

### Copy files
The files:
- `EscRunner.java`
- `EscVerify.java`
- `RunTimeEscVerificationCodeGenerator.java`

Must be copied into the project that you wish to run under the package `uk.gre.ac.openjmlsec.gen`.

### Running JML4SEC

The `openjml` command can be used to run our tool.
The command line looks like this:
`./openjml --JML4SEC /PATH/TO/SOURCE/FILE.java /PATH/TO/OUTPUT/FOLDER/`

Where `/PATH/TO/SOURCE/FILE.java` is the source file you wish to generate a new source for, witch will be created in `/PATH/TO/OUTPUT/FOLDER/` with the same filename.

## Running files
The command `./openjml-run` is used to run this file, however the files must be build before, this can be done by eclipse or at the command line.
The command line arguments for running in the development environment Specs can be passed by `-Dopenjml.eclipseSpecsProjectLocation=` `/PATH/TO/PROJECT/Specs`

The parameters for our tool are:
- `-DOpenJMLSec_LogFile=` the location to a file for OpenJML output to be put into at run-time, default is `null` and outputs to `System.err`.
- `-OpenJMLSec_SourceFolder=` the location to the source folder of the project, default is `"./"`.
- `-OpenJMLSec_openjml=` the location to the openjml bash script, default is `"openjml"`.

Additionally, the compiled versions of initial source of the files must be on the class path or their specification must be place within the `specs` folder.
The reason for this is when looking for external classes (such as packages or modules), OpenJML will attempt to initially look within the `specs` folder to find the specifications for this external class.
If this fails, it will then look on the `classpath` for this file and any OpenJML comments within that class.

# Classes

There are example classes located in the `Classes` folder.
To run the examples, copy a built release of OpenJML to The root of the project, and run commands within the release folder.

Example command line:

`./openjml --JML4SEC ../src/testclasses/MalInput.java ../src/generatedClasses`

`./openjml-run -DOpenJMLSec_openjml=./openjml -DOpenJMLSec_LogFile=./OpenJMLSECLog.txt -DOpenJMLSec_SourceFolder=../src -classpath ../bin generatedClasses.MalInput`

