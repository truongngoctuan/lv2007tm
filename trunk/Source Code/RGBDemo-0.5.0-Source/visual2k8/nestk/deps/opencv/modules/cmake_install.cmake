# Install script for directory: C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules

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

IF(NOT CMAKE_INSTALL_LOCAL_ONLY)
  # Include the install script for each subdirectory.
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/calib3d/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/core/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/features2d/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/flann/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/ffmpeg/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/highgui/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/imgproc/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/legacy/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/contrib/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/ml/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/objdetect/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/video/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/haartraining/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/traincascade/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/gpu/cmake_install.cmake")

ENDIF(NOT CMAKE_INSTALL_LOCAL_ONLY)

