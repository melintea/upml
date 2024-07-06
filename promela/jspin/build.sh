#!/bin/env bash
# Has to be ran inside of the jspin unzipped directory! Linux only, not Mac
javac jspin/*.java
javac spinSpider/*.java
javac filterSpin/*.java
jar cfm jSpin.jar jspin/MANIFEST.MF jspin/*.class spinSpider/*.class filterSpin/*.class

