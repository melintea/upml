Fetched from [kocsenc](https://gist.github.com/kocsenc/10130261#file-blueprint-md)



jSpin for Mac and Linux
====================
This is a quick simple guide to getting [jSpin](http://code.google.com/p/jspin/) setup for Mac and Linux.

Prereq's
--------
You will need:
  * Java (1.5 +)
  * GCC Compiler (most should have this already)
  * Mac only: [brew](http://brew.sh)

Install for Mac
----------------
1. `brew install spin`
2. At this point you can just run `spin file.pml` to run spin. If you still want jSpin, carry on.
3. Download the `jspin*.zip` file from their [download site](http://code.google.com/p/jspin/downloads/list) or  [direct link for 5.0](https://storage.googleapis.com/google-code-archive-downloads/v2/code.google.com/jspin/jspin-5-0.zip)
4. Unzip it
5. Download `config.cfg` below and place it in the unzipped folder.
6. Replace `config.cfg` **line 12 =>** `SPIN=/usr/local/bin/spin`
6. Replace `config.cfg` **line 27 =>** `C_COMPILER=/usr/bin/gcc`
7. Double click on `jSpin.jar` or run `java -jar jSpin.jar`

Install for Linux
-----------------
1. [Download the sources and follow the instructions on their site](http://spinroot.com/spin/Man/README.html#S1a). Do not install `iSpin` just spin. The file `build.sh` may be helpful for you.
2. Make sure you make the `spin` executable available at `/usr/bin/spin`. You can use `symlinks`.
3. Download the `jspin*.zip` file from their [download site](http://code.google.com/p/jspin/downloads/list) or  [direct link for 5.0](https://storage.googleapis.com/google-code-archive-downloads/v2/code.google.com/jspin/jspin-5-0.zip)
4. Unzip it
5. Download `config.cfg` below and place it in the unzipped folder.
6. Pay attention to **line 12** of `config.cfg` as it should link to the spin executable you installed earlier.
1. Double click on `jSpin.jar` or run `java -jar jSpin.jar`


Troubleshooting
---------------

> The best I got for troubleshooting is to simply walk through the `config.cfg` file and make sure all the paths check out to actual binaries. Under no circumstance try to install windows for this to work. You can do it.

Also

> Remember jSpin is a java based IDE for spin. You **don't** need to use it! You can also use `spin` in the command line to compile and run your promela files (C style) or other IDE's such as `iSpin`.

