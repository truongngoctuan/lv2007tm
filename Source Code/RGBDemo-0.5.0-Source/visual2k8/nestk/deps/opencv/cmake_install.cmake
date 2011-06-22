# Install script for directory: C:/RGBDemo-0.5.0-Source/nestk/deps/opencv

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

IF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "Unspecified")
  list(APPEND CPACK_ABSOLUTE_DESTINATION_FILES
   "C:/Program Files (x86)/RGBDemo/OpenCVConfig.cmake")
FILE(INSTALL DESTINATION "C:/Program Files (x86)/RGBDemo" TYPE FILE FILES "C:/RGBDemo-0.5.0-Source/visual2k8/win-install/OpenCVConfig.cmake")
ENDIF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "Unspecified")

IF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "Unspecified")
  list(APPEND CPACK_ABSOLUTE_DESTINATION_FILES
   "C:/Program Files (x86)/RGBDemo/3rdparty/lib/videoInput.lib;C:/Program Files (x86)/RGBDemo/3rdparty/lib/videoInput64.lib")
FILE(INSTALL DESTINATION "C:/Program Files (x86)/RGBDemo/3rdparty/lib" TYPE FILE FILES
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/3rdparty/lib/videoInput.lib"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/3rdparty/lib/videoInput64.lib"
    )
ENDIF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "Unspecified")

IF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "Unspecified")
  list(APPEND CPACK_ABSOLUTE_DESTINATION_FILES
   "C:/Program Files (x86)/RGBDemo/3rdparty/include/videoInput.h")
FILE(INSTALL DESTINATION "C:/Program Files (x86)/RGBDemo/3rdparty/include" TYPE FILE FILES "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/3rdparty/include/videoInput.h")
ENDIF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "Unspecified")

IF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "Unspecified")
  list(APPEND CPACK_ABSOLUTE_DESTINATION_FILES
   "C:/Program Files (x86)/RGBDemo/include/cvconfig.h")
FILE(INSTALL DESTINATION "C:/Program Files (x86)/RGBDemo/include" TYPE FILE FILES "C:/RGBDemo-0.5.0-Source/visual2k8/cvconfig.h")
ENDIF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "Unspecified")

IF(NOT CMAKE_INSTALL_LOCAL_ONLY)
  # Include the install script for each subdirectory.
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/include/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/modules/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/doc/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/data/cmake_install.cmake")
  INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/opencv/3rdparty/cmake_install.cmake")

ENDIF(NOT CMAKE_INSTALL_LOCAL_ONLY)

