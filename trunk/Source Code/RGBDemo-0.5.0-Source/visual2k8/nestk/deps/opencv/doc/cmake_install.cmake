# Install script for directory: C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc

# Set the install prefix
IF(NOT DEFINED CMAKE_INSTALL_PREFIX)
  SET(CMAKE_INSTALL_PREFIX "C:/Program Files (x86)/RGBDemo")
ENDIF(NOT DEFINED CMAKE_INSTALL_PREFIX)
STRING(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
IF(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  IF(BUILD_TYPE)
    STRING(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  ELSE(BUILD_TYPE)
    SET(CMAKE_INSTALL_CONFIG_NAME "Release")
  ENDIF(BUILD_TYPE)
  MESSAGE(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
ENDIF(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)

# Set the component getting installed.
IF(NOT CMAKE_INSTALL_COMPONENT)
  IF(COMPONENT)
    MESSAGE(STATUS "Install component: \"${COMPONENT}\"")
    SET(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  ELSE(COMPONENT)
    SET(CMAKE_INSTALL_COMPONENT)
  ENDIF(COMPONENT)
ENDIF(NOT CMAKE_INSTALL_COMPONENT)

IF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "main")
  FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/doc" TYPE FILE FILES
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/haartraining.htm"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/CMakeLists.txt"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/license.txt"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/packaging.txt"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/README.txt"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/opencv.jpg"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/opencv-logo.png"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/opencv-logo2.png"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/opencv.pdf"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/opencv_cheatsheet.pdf"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/pattern.pdf"
    )
ENDIF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "main")

IF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "main")
  FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/doc/papers" TYPE FILE FILES
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/papers/algo_tracking.pdf"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/papers/camshift.pdf"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/papers/avbpa99.ps"
    )
ENDIF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "main")

IF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "main")
  FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/doc/vidsurv" TYPE FILE FILES
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/vidsurv/Blob_Tracking_Modules.doc"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/vidsurv/Blob_Tracking_Tests.doc"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/doc/vidsurv/TestSeq.doc"
    )
ENDIF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "main")

