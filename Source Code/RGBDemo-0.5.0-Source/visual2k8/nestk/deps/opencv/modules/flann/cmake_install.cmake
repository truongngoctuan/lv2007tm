# Install script for directory: C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann

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
  IF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Dd][Ee][Bb][Uu][Gg])$")
    FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY OPTIONAL FILES "C:/RGBDemo-0.5.0-Source/visual2k8/lib/Debug/opencv_flann220d.lib")
  ENDIF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Dd][Ee][Bb][Uu][Gg])$")
  IF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee])$")
    FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY OPTIONAL FILES "C:/RGBDemo-0.5.0-Source/visual2k8/lib/Release/opencv_flann220.lib")
  ENDIF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee])$")
  IF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Mm][Ii][Nn][Ss][Ii][Zz][Ee][Rr][Ee][Ll])$")
    FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY OPTIONAL FILES "C:/RGBDemo-0.5.0-Source/visual2k8/lib/MinSizeRel/opencv_flann220.lib")
  ENDIF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Mm][Ii][Nn][Ss][Ii][Zz][Ee][Rr][Ee][Ll])$")
  IF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ww][Ii][Tt][Hh][Dd][Ee][Bb][Ii][Nn][Ff][Oo])$")
    FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY OPTIONAL FILES "C:/RGBDemo-0.5.0-Source/visual2k8/lib/RelWithDebInfo/opencv_flann220.lib")
  ENDIF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ww][Ii][Tt][Hh][Dd][Ee][Bb][Ii][Nn][Ff][Oo])$")
  IF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee],[Rr][Ee][Ll][Ww][Ii][Tt][Hh][Dd][Ee][Bb][Ii][Nn][Ff][Oo])$")
    FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY OPTIONAL FILES "C:/RGBDemo-0.5.0-Source/visual2k8/lib/Release,RelWithDebInfo/opencv_flann220.lib")
  ENDIF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee],[Rr][Ee][Ll][Ww][Ii][Tt][Hh][Dd][Ee][Bb][Ii][Nn][Ff][Oo])$")
ENDIF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "main")

IF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "main")
  IF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Dd][Ee][Bb][Uu][Gg])$")
    FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/bin" TYPE SHARED_LIBRARY FILES "C:/RGBDemo-0.5.0-Source/visual2k8/bin/Debug/opencv_flann220d.dll")
  ENDIF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Dd][Ee][Bb][Uu][Gg])$")
  IF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee])$")
    FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/bin" TYPE SHARED_LIBRARY FILES "C:/RGBDemo-0.5.0-Source/visual2k8/bin/Release/opencv_flann220.dll")
  ENDIF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee])$")
  IF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Mm][Ii][Nn][Ss][Ii][Zz][Ee][Rr][Ee][Ll])$")
    FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/bin" TYPE SHARED_LIBRARY FILES "C:/RGBDemo-0.5.0-Source/visual2k8/bin/MinSizeRel/opencv_flann220.dll")
  ENDIF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Mm][Ii][Nn][Ss][Ii][Zz][Ee][Rr][Ee][Ll])$")
  IF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ww][Ii][Tt][Hh][Dd][Ee][Bb][Ii][Nn][Ff][Oo])$")
    FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/bin" TYPE SHARED_LIBRARY FILES "C:/RGBDemo-0.5.0-Source/visual2k8/bin/RelWithDebInfo/opencv_flann220.dll")
  ENDIF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ww][Ii][Tt][Hh][Dd][Ee][Bb][Ii][Nn][Ff][Oo])$")
  IF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee],[Rr][Ee][Ll][Ww][Ii][Tt][Hh][Dd][Ee][Bb][Ii][Nn][Ff][Oo])$")
    FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/bin" TYPE SHARED_LIBRARY FILES "C:/RGBDemo-0.5.0-Source/visual2k8/bin/Release,RelWithDebInfo/opencv_flann220.dll")
  ENDIF("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee],[Rr][Ee][Ll][Ww][Ii][Tt][Hh][Dd][Ee][Bb][Ii][Nn][Ff][Oo])$")
ENDIF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "main")

IF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "main")
  FILE(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/opencv2/flann" TYPE FILE FILES
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/allocator.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/all_indices.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/autotuned_index.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/composite_index.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/dist.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/flann.hpp"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/flann_base.hpp"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/general.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/ground_truth.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/hdf5.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/heap.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/index_testing.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/kdtree_index.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/kmeans_index.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/linear_index.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/logger.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/matrix.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/nn_index.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/object_factory.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/random.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/result_set.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/sampling.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/saving.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/simplex_downhill.h"
    "C:/RGBDemo-0.5.0-Source/nestk/deps/opencv/modules/flann/include/opencv2/flann/timer.h"
    )
ENDIF(NOT CMAKE_INSTALL_COMPONENT OR "${CMAKE_INSTALL_COMPONENT}" STREQUAL "main")

