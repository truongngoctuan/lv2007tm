INCLUDE_DIRECTORIES("C:/RGBDemo-0.5.0-Source/nestk")
INCLUDE_DIRECTORIES("C:/RGBDemo-0.5.0-Source/visual2k8/nestk")

SET(NESTK_EXTRA_CMAKE_CXX_FLAGS  
    CACHE STRING "Extra flags appended to CMAKE_CXX_FLAGS" )
SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} " )

INCLUDE("C:/RGBDemo-0.5.0-Source/visual2k8/nestk/deps/cmake/UseNestkDeps.cmake")

IF(IS_DIRECTORY "C:/RGBDemo-0.5.0-Source/nestk/ntk/private")
  ADD_DEFINITIONS(-DNESTK_PRIVATE)
  SET(HAVE_NESTK_PRIVATE 1 CACHE INTERNAL "Nestk private features are available")
ENDIF()
