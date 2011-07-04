/**
 * This file is part of the nestk library.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * Author: Nicolas Burrus <nicolas.burrus@uc3m.es>, (C) 2010
 */

// For QTCreator
 //#define NESTK_USE_PCL

#include "relative_pose_estimator.h"

#include <ntk/utils/time.h>
#include <ntk/utils/stl.h>
#include <ntk/stats/histogram.h>
#include <ntk/numeric/levenberg_marquart_minimizer.h>
#include <ntk/utils/opencv_utils.h>
#include <ntk/mesh/mesh.h>

namespace ntk
{

/*!
 * Compute the projection error of a 3D point cloud on a new image.
 * If feature points on the new image have depth information, it
 * will be taken into account.
 */
struct reprojection_error_3d : public ntk::CostFunction
{
  reprojection_error_3d(const Pose3D& initial_pose,
                        const std::vector<cv::Point3f>& ref_points,
                        const std::vector<cv::Point3f>& img_points)
    : CostFunction(6, ref_points.size()*3),
      initial_pose(initial_pose),
      ref_points(ref_points),
      img_points(img_points)
  {
    ntk_assert(ref_points.size() == img_points.size(), "Invalid matches");
  }

  virtual void evaluate (const std::vector< double > &x, std::vector< double > &fx) const
  {
    const bool use_depth = true;
    Pose3D new_pose = initial_pose;
    new_pose.applyTransformAfter(cv::Vec3f(x[3],x[4],x[5]), cv::Vec3f(x[0],x[1],x[2]));
    int err_i = 0;
    std::fill(stl_bounds(fx), 0);
    foreach_idx(p_i, ref_points)
    {
      const cv::Point3f& ref_point = ref_points[p_i];
      const cv::Point3f& img_point = img_points[p_i];
      cv::Point3f proj_p = new_pose.projectToImage(ref_point);
      fx[err_i*3] = (proj_p.x - img_point.x);
      fx[err_i*3+1] = (proj_p.y - img_point.y);
      if (use_depth && img_point.z > 1e-5 && ref_point.z > 1e-5)
        fx[err_i*3+2] = new_pose.meanFocal() * (proj_p.z - img_point.z);
      else
        fx[err_i*3+2] = 0;
      err_i = err_i + 1;
    }
  }

private:
  const Pose3D& initial_pose;
  const std::vector<cv::Point3f>& ref_points;
  const std::vector<cv::Point3f>& img_points;
};

// atomic mean square pose estimation.
double rms_optimize_3d(Pose3D& pose3d,
                       const std::vector<cv::Point3f>& ref_points,
                       const std::vector<cv::Point3f>& img_points)
{
  std::vector<double> fx;
  std::vector<double> initial(6);
  reprojection_error_3d f(pose3d, ref_points, img_points);//cost function
  LevenbergMarquartMinimizer optimizer;//minimize cost function
  std::fill(stl_bounds(initial), 0);
  fx.resize(ref_points.size()*3);
  optimizer.minimize(f, initial);
  optimizer.diagnoseOutcome();
  f.evaluate(initial, fx);

  double error = f.outputNorm(initial);

  pose3d.applyTransformAfter(cv::Vec3f(initial[3],initial[4],initial[5]), cv::Vec3f(initial[0], initial[1], initial[2]));
  return error;
}

double rms_optimize_ransac(Pose3D& pose3d,
                           const std::vector<cv::Point3f>& ref_points,
                           const std::vector<cv::Point3f>& img_points,
                           std::vector<bool>& valid_points)
{
  // One centimeter. 1000*1000 comes from the error scale factor
  // in rms_optimize.
  const double rms_err_threshold = 5;
  const double compat_err_threshold = 3;
  const int max_iterations = 200;
  const int min_support_points = std::max(7, int(ref_points.size()/20));
  const float min_consensus_support_percent = 0.05;

  ntk_assert(ref_points.size() > min_support_points, "Not enough points.");

  cv::RNG rgen;
  double best_error = FLT_MAX;
  Pose3D best_pose = pose3d;
  Pose3D current_pose = pose3d;
  std::vector<cv::Point3f> current_ref_points;
  std::vector<cv::Point3f> current_img_points;
  std::set<int> best_indices;
  std::set<int> indices;

  for (int it = 0; it < max_iterations && best_error > 0.01; ++it)
  {
    // initial set and model
    draw_k_different_numbers(rgen, indices, min_support_points, ref_points.size());

    current_pose = pose3d;
    current_ref_points.clear();
    current_img_points.clear();
    current_ref_points.reserve(indices.size());
    current_img_points.reserve(indices.size());
    foreach_const_it(it, indices, std::set<int>)
    {
      current_ref_points.push_back(ref_points[*it]);
      current_img_points.push_back(img_points[*it]);
    }

    double initial_error = rms_optimize_3d(current_pose, current_ref_points, current_img_points);
    // Base solution not good enough.
    if (initial_error > rms_err_threshold)
      continue;

    ntk_dbg_print(initial_error, 2);
    // determine consensus set.
    foreach_idx(index, ref_points)
    {
      if (indices.find(index) != indices.end())
        continue;

      cv::Point3f proj_p = current_pose.projectToImage(ref_points[index]);
      double error = 0;
      error += ntk::math::sqr(proj_p.x - img_points[index].x);
      error += ntk::math::sqr(proj_p.y - img_points[index].y);
      if (img_points[index].z > 1e-5)
        error += ntk::math::sqr((proj_p.z - img_points[index].z)*current_pose.meanFocal());
      error = sqrt(error);

      if (error < compat_err_threshold)
        indices.insert(index);
    }

    ntk_dbg_print(indices.size(), 2);
    if (indices.size() < (min_consensus_support_percent*ref_points.size()))
      continue;

    current_ref_points.clear();
    current_img_points.clear();
    foreach_const_it(it, indices, std::set<int>)
    {
      current_ref_points.push_back(ref_points[*it]);
      current_img_points.push_back(img_points[*it]);
    }
    // current_pose = pose3d;

    double iteration_error = rms_optimize_3d(current_pose, current_ref_points, current_img_points);
    ntk_dbg_print(iteration_error, 2);
    if (iteration_error < best_error)
    {
      best_error = iteration_error;
      best_pose = current_pose;
      best_indices = indices;
    }
  } // end ransac loop

  valid_points.resize(ref_points.size(), false);
  foreach_const_it(it, best_indices, std::set<int>)
      valid_points[*it] = true;
  ntk_dbg_print(best_indices.size(), 2);
  pose3d = best_pose;
  return best_error;
}

} // ntk

namespace ntk
{

bool RelativePoseEstimatorFromFile::estimateNewPose(const RGBDImage& image)
{
  ntk_ensure(image.hasDirectory(), "Only works in fake mode!");
  m_current_pose.parseAvsFile((image.directory() + "/relative_pose.avs").c_str());
  return true;
}

bool RelativePoseEstimatorFromDelta::estimateNewPose(const RGBDImage& image)
{
  m_current_pose.applyTransformAfter(m_delta_pose);
  return true;
}

  
/*!
 * Compute the number of closest feature matches for each previous view.
 */
int RelativePoseEstimatorFromImage::computeNumMatchesWithPrevious(const RGBDImage& image,
                              const FeatureSet& features,
							  std::vector<cv::DMatch>& best_matches)
{
  const int min_number_of_matches = 30;
  int best_prev_image = 0;
  // If at least 30 matches have been found with one image, stop searching.
  // Start with the last one, more likely to have a similar point of view.
  //int min_i = (m_features.size() > 5) ? m_features.size() - 5 : 0;
  int min_i = 0;
  for (int i = m_features.size()-1;
       i >= min_i && best_matches.size() < min_number_of_matches;
       --i)
  {
    std::vector<cv::DMatch> current_matches;
    m_features[i].matchWith(features, current_matches, 0.6*0.6);

    ntk_dbg_print(current_matches.size(), 1);
    if (current_matches.size() > best_matches.size())
    {
      best_prev_image = i;
      best_matches = current_matches;
    }
  }
  return best_prev_image;
}

bool RelativePoseEstimatorFromImage::
estimateDeltaPose(Pose3D& new_rgb_pose,
                  const RGBDImage& image,
                  const FeatureSet& image_features,
                  const std::vector<cv::DMatch>& best_matches,
                  int closest_view_index)
{
  const float err_threshold = 5;

  ntk_dbg_print(new_rgb_pose, 2);
  const ImageData& ref_image_data = m_image_data[closest_view_index];

  ntk_dbg_print(best_matches.size(), 2);
  if (best_matches.size() < 10)
  {
    ntk_dbg(1) << "Not enough point matches (< 10)";
    return false;
  }

  std::vector<cv::Point3f> ref_points;
  std::vector<cv::Point3f> img_points;
  std::vector<cv::KeyPoint> ref_keypoints;
  std::vector<cv::KeyPoint> img_keypoints;

  foreach_idx(i, best_matches)
  {
    const cv::DMatch& m = best_matches[i];
    const FeatureSet& ref_set = m_features[closest_view_index];
    const FeatureLocation& ref_loc = ref_set.locations()[m.trainIdx];
    const FeatureLocation& img_loc = image_features.locations()[m.queryIdx];

	////tntuan
	//if (ref_loc.depth > 1.0f || img_loc.depth > 1.0f)
	//	continue;

    ntk_assert(ref_loc.depth > 0, "Match without depth, should not appear");

    cv::Point3f img3d (img_loc.pt.x,
                   img_loc.pt.y,
                   img_loc.depth);

    ref_points.push_back(ref_loc.p3d);
    img_points.push_back(img3d);
  }

  ntk_dbg_print(ref_points.size(), 1);
  if (ref_points.size() < 10)
  {
    ntk_dbg(2) << "Not enough matches with depth";
    return false;
  }

  // double error = rms_optimize_3d(new_pose, ref_points, img_points);
  std::vector<bool> valid_points;
  double error = rms_optimize_ransac(new_rgb_pose, ref_points, img_points, valid_points);

  ntk_dbg_print(error, 1);
  ntk_dbg_print(new_rgb_pose, 2);

  if (error < err_threshold)
    return true;
  else
    return false;
}

bool RelativePoseEstimatorFromImage::estimateNewPose(const RGBDImage& image)
{
  ntk_ensure(image.calibration(), "Image must be calibrated.");
  if (!m_current_pose.isValid())
  {
    m_current_pose = *image.calibration()->depth_pose;
  }

  ntk_ensure(image.mappedDepth().data, "Image must have depth mapping.");
  TimeCount tc_extractFromImage("extractFromImage", 2);
  FeatureSet image_features;
  image_features.extractFromImage(image, m_feature_parameters);
  tc_extractFromImage.stop();

  Pose3D new_pose = *image.calibration()->depth_pose;
  Pose3D new_rgb_pose = new_pose;
  new_rgb_pose.toRightCamera(image.calibration()->rgb_intrinsics,
                             image.calibration()->R, image.calibration()->T);//?? dư??
  bool pose_ok = true;

  int closest_view_index = -1;

  
  if (m_image_data.size() > 0)
  {
	  TimeCount tc_computeNumMatchesWithPrevious("computeNumMatchesWithPrevious", 2);
    std::vector<cv::DMatch> best_matches;
    closest_view_index = computeNumMatchesWithPrevious(image, image_features, best_matches);
    ntk_dbg_print(closest_view_index, 1);
    ntk_dbg_print(best_matches.size(), 1);

	////tntuan
	//std::vector<cv::DMatch> filter_best_matches;
	//for (int i = 0; i < best_matches.size(); i++)
	//{
	//	//best_matches[i].trainIdx;
	//	image. best_matches[i].queryIdx
	//}

	//ntk_dbg_print(filter_best_matches.size(), 1);

    new_pose = m_image_data[closest_view_index].depth_pose;
    new_rgb_pose = new_pose;
    new_rgb_pose.toRightCamera(image.calibration()->rgb_intrinsics,
                               image.calibration()->R, image.calibration()->T);
	tc_computeNumMatchesWithPrevious.stop();

	TimeCount tc_estimateDeltaPose("estimateDeltaPose", 2);
    if (best_matches.size() > 0)
    {
      // Estimate the relative pose w.r.t the closest view.
      if (!estimateDeltaPose(new_rgb_pose, image, image_features, best_matches, closest_view_index))
        pose_ok = false;
      new_pose = new_rgb_pose;
      new_pose.toLeftCamera(image.calibration()->depth_intrinsics,
                            image.calibration()->R, image.calibration()->T);

    }
    else
    {
      pose_ok = false;
    }
	tc_estimateDeltaPose.stop();
  }
  

  if (pose_ok)
  {
    if (m_use_icp)
      pose_ok &= optimizeWithICP(image, new_pose, closest_view_index);
  }

  if (pose_ok)
  {
    new_rgb_pose = new_pose;
    new_rgb_pose.toRightCamera(image.calibration()->rgb_intrinsics,
                               image.calibration()->R, image.calibration()->T);

    ImageData image_data;
    image.rgb().copyTo(image_data.color);
    image_data.depth_pose = new_pose;
    m_current_pose = new_pose;
    image_features.compute3dLocation(new_rgb_pose);
    m_features.push_back(image_features);
    ntk_dbg_print(image_features.locations().size(), 1);
    m_image_data.push_back(image_data);
    return true;
  }
  else
    return false;
}

void RelativePoseEstimatorFromImage::CalulatePairs(const Pose3D& depth_pose1, const Pose3D& depth_pose2,
							   const FeatureSet& image_features1, const FeatureSet& image_features2,
							   const std::vector<cv::DMatch>& best_matches,
							   std::vector<cv::Point3f>& ref_points, std::vector<cv::Point3f>& img_points)
{
	Pose3D Tempdepth_pose1 = depth_pose1;
	Pose3D Tempdepth_pose2 = depth_pose2;

	FeatureSet Tempimage_features1 = image_features1;
	FeatureSet Tempimage_features2 = image_features2;
	Tempimage_features1.compute3dLocation(Tempdepth_pose1);
	Tempimage_features2.compute3dLocation(Tempdepth_pose2);

	foreach_idx(i, best_matches)
	{
		const cv::DMatch& m = best_matches[i];
		const FeatureSet& ref_set = Tempimage_features1;
		const FeatureSet& img_set = Tempimage_features2;
		const FeatureLocation& ref_loc = ref_set.locations()[m.trainIdx];
		const FeatureLocation& img_loc = img_set.locations()[m.queryIdx];
		//
		////cv::Point3f img3d (img_loc.pt.x, img_loc.pt.y, img_loc.depth);
		////2d --> 3d
		//cv::Point3f ref3d = depth_pose1.unprojectFromImage(cv::Point2f(ref_loc.pt.x, ref_loc.pt.y), ref_loc.depth);
		//cv::Point3f img3d = depth_pose2.unprojectFromImage(cv::Point2f(img_loc.pt.x, img_loc.pt.y), img_loc.depth);

		//ref_points.push_back(ref3d);
		//img_points.push_back(img3d);

		ref_points.push_back(ref_loc.p3d);
		img_points.push_back(img_loc.p3d);
	}
}

boost::mutex mtcomputeNumMatchesWithPrevious;
bool RelativePoseEstimatorFromImage::estimateNewPose(const RGBDImage& image, Pose3D& current_pose_final, 
													 //std::vector<cv::Point3f>& ref_points, std::vector<cv::Point3f>& img_points,
													 int& closest_view_index)
{
  ntk_ensure(image.calibration(), "Image must be calibrated.");
  if (!m_current_pose.isValid())
  {
    m_current_pose = *image.calibration()->depth_pose;
  }

  ntk_ensure(image.mappedDepth().data, "Image must have depth mapping.");
  TimeCount tc_extractFromImage("extractFromImage", 2);
  FeatureSet image_features;
  image_features.extractFromImage(image, m_feature_parameters);
  tc_extractFromImage.stop();

  Pose3D new_pose = *image.calibration()->depth_pose;
  Pose3D new_rgb_pose = new_pose;
  new_rgb_pose.toRightCamera(image.calibration()->rgb_intrinsics,
                             image.calibration()->R, image.calibration()->T);//?? dư??
  bool pose_ok = true;

  m_closest_view_index = closest_view_index = -1;
	std::vector<cv::DMatch> best_matches;
  boost::unique_lock<boost::mutex> lock(mtcomputeNumMatchesWithPrevious);
  if (m_image_data.size() > 0)
  {
	  TimeCount tc_computeNumMatchesWithPrevious("computeNumMatchesWithPrevious", 2);
    
    closest_view_index = computeNumMatchesWithPrevious(image, image_features, best_matches);
    ntk_dbg_print(closest_view_index, 1);
    ntk_dbg_print(best_matches.size(), 1);

    new_pose = m_image_data[closest_view_index].depth_pose;
    new_rgb_pose = new_pose;
    new_rgb_pose.toRightCamera(image.calibration()->rgb_intrinsics,
                               image.calibration()->R, image.calibration()->T);
	tc_computeNumMatchesWithPrevious.stop();

	TimeCount tc_estimateDeltaPose("estimateDeltaPose", 2);
    if (best_matches.size() > 0)
    {
      // Estimate the relative pose w.r.t the closest view.
      if (!estimateDeltaPose(new_rgb_pose, image, image_features, best_matches, closest_view_index))
        pose_ok = false;
      new_pose = new_rgb_pose;
      new_pose.toLeftCamera(image.calibration()->depth_intrinsics,
                            image.calibration()->R, image.calibration()->T);

    }
    else
    {
      pose_ok = false;
    }

	  if (pose_ok)
  {
    //if (m_use_icp)
	  //if (m_closest_view_index != -1 && true)
	  if(true)
		pose_ok &= optimizeWithICP(image, new_pose, closest_view_index);
  }

	m_closest_view_index = closest_view_index;
	m_best_matches = best_matches;
	image.copyTo(m_image);

    image.rgb().copyTo(m_Newimage_data.color);
    m_Newimage_data.depth_pose = new_pose;
	m_Newfeatures = image_features;

	tc_estimateDeltaPose.stop();

  }



  if (pose_ok)
  {
    new_rgb_pose = new_pose;
    new_rgb_pose.toRightCamera(image.calibration()->rgb_intrinsics,
                               image.calibration()->R, image.calibration()->T);


    ImageData image_data;
    image.rgb().copyTo(image_data.color);
	image.mappedDepth().copyTo(image_data.depth);
    image_data.depth_pose = new_pose;
    //m_current_pose = new_pose;
	current_pose_final = new_pose;
    image_features.compute3dLocation(new_rgb_pose);
    m_features.push_back(image_features);
    ntk_dbg_print(image_features.locations().size(), 1);
    m_image_data.push_back(image_data);

	

    return true;
  }
  else
    return false;
}

void RelativePoseEstimatorFromImage::CalulatePairs(bool bIsAligned, 
	  std::vector<cv::Point3f>& ref_points, std::vector<cv::Point3f>& img_points)
{
	if (m_closest_view_index != -1)
	{//loai bo truogn hop dau tien ko co frame truoc do 

		//tinh lai cai new_pose giong nhu trong ha`m addnewpose
		if (bIsAligned)
		{
			Pose3D depth_pose2 = m_current_pose;
			depth_pose2.applyTransformBefore(m_image_data[m_closest_view_index].depth_pose);

			Pose3D depth_pose22 = m_current_pose;
			depth_pose22.applyTransformBefore(m_Newimage_data.depth_pose);

			CalulatePairs(depth_pose2, depth_pose22,
				m_features[m_closest_view_index], m_Newfeatures,
				m_best_matches,
				ref_points, img_points);
		}
		else
		{
			Pose3D depth_pose2 = m_current_pose;
			Pose3D depth_pose22 = m_current_pose;

			CalulatePairs(depth_pose2, depth_pose22,
				m_features[m_closest_view_index], m_Newfeatures,
				m_best_matches,
				ref_points, img_points);
		}
	}
}

void RelativePoseEstimatorFromImage::reset()
{
  m_features.clear();
  m_image_data.clear();
}

void rgbdImageToPointCloud(std::vector<Point3f>& points,
						   const cv::Mat1f& depth,
                           const Pose3D& pose)
{
  for (int r = 0; r < depth.rows; r++)
  for (int c = 0; c < depth.cols; c++)
  {
    float d = depth(r,c);
    if (d < 1e-5 || d > 1.0f)
      continue;
    Point3f p = pose.unprojectFromImage(Point2f(c,r),d * 1000.0f);
    points.push_back(p);
  }
}


void PointCloudToPlyFiles2(std::vector<Point3f>& points,
						  std::string strFileName)
{
	ofstream ply_file(strFileName.c_str());

	ply_file << "ply\n";
	ply_file << "format ascii 1.0\n";
	ply_file << "element vertex " << points.size() << "\n";
	ply_file << "property float32 x\n";
	ply_file << "property float32 y\n";
	ply_file << "property float32 z\n";
	ply_file << "property uchar red\n";
	ply_file << "property uchar green\n";
	ply_file << "property uchar blue\n";
	ply_file << "end_header\n";

	foreach_idx(i, points)
	{
		//ply_file << points[i].x * 1000.0f << " " << points[i].y * 1000.0f << " " << points[i].z * 1000.0f;
		ply_file << points[i].x << " " << points[i].y<< " " << points[i].z;

		ply_file << " " << 0 << " " << 0 << " " << 0;

		ply_file << "\n";
	}

	ply_file.close();
}

void getrtMatrixFromFile(string str, cv::Vec3f& translation, cv::Mat1d& rotation_matrix)
{
	ifstream ifs (str.c_str());
	ifs >>rotation_matrix[0][0]>>rotation_matrix[0][1]>>rotation_matrix[0][2]>>translation[0];
	ifs >>rotation_matrix[1][0]>>rotation_matrix[1][1]>>rotation_matrix[1][2]>>translation[1];
	ifs >>rotation_matrix[2][0]>>rotation_matrix[2][1]>>rotation_matrix[2][2]>>translation[2];
	ifs.close();
}

void getrtMatrixFromFile(string str, cv::Mat1f& H)
{
	ifstream ifs (str.c_str());
	ifs >>H[0][0]>>H[0][1]>>H[0][2]>>H[0][3];
	ifs >>H[1][0]>>H[1][1]>>H[1][2]>>H[1][3];
	ifs >>H[2][0]>>H[2][1]>>H[2][2]>>H[2][3];
	ifs >>H[3][0]>>H[3][1]>>H[3][2]>>H[3][3];
	ifs.close();
}

bool RelativePoseEstimatorFromImage::optimizeWithICP(const RGBDImage& image, Pose3D& depth_pose, int closest_view_index)
{
	std::vector<cv::Point3f> ref_points;
	std::vector<cv::Point3f> img_points;
	CalulatePairs(false, ref_points, img_points);
	//filter get 4 pairs
	//return InitFeaturePairs(ref_points, img_points);
	//do icp, 
	//update depth_pose
	//
	//std::vector<Point3f> pts1;
	//std::vector<Point3f> pts2;
	////depth_pose.toRightCamera(image.calibration()->rgb_intrinsics,
 ////                            image.calibration()->R, image.calibration()->T);

	//Pose3D depth_pose1 = m_image_data[closest_view_index].depth_pose;

	////depth_pose1.toRightCamera(image.calibration()->rgb_intrinsics,
 ////                            image.calibration()->R, image.calibration()->T);


	//rgbdImageToPointCloud(pts1, m_image_data[closest_view_index].depth, depth_pose1);
	//rgbdImageToPointCloud(pts2, image.mappedDepth(), depth_pose);
	//
	//PointCloudToPlyFiles2(pts1, "temp1.ply");
	//PointCloudToPlyFiles2(pts2, "temp2.ply");

	//ofstream ofs("listplytemp.txt");
	//ofs<<2<<endl;
	//ofs<<"temp1.ply"<<endl;
	//ofs<<"temp2.ply"<<endl;

	//bool result = MyAlign::Auto("listplytemp.txt", "config");

	//if (result)
	//{
	//	//cap nhat pose
	//	cv::Mat1f H1(4, 4), H2(4, 4);
	//	getrtMatrixFromFile("config\\temp1.txt", H1);
	//	getrtMatrixFromFile("config\\temp2.txt", H2);

	//	cout <<H2[0][0]<<" "<<H2[0][1]<<" "<<H2[0][2]<<" "<<H2[0][3]<<endl;
	//	cout <<H2[1][0]<<" "<<H2[1][1]<<" "<<H2[1][2]<<" "<<H2[1][3]<<endl;
	//	cout <<H2[2][0]<<" "<<H2[2][1]<<" "<<H2[2][2]<<" "<<H2[2][3]<<endl;
	//	cout <<H2[3][0]<<" "<<H2[3][1]<<" "<<H2[3][2]<<" "<<H2[3][3]<<endl;
	//	cout<<"--------------"<<endl;

	//	cv::Vec3f translation;
	//	cv::Mat1d rotation_matrix(3, 3, 0.0f);
	//	getrtMatrixFromFile("config\\temp2.txt", translation, rotation_matrix);

	//	//translation[0] = translation[0] / 1000.0f;
	//	//translation[1] = translation[1] / 1000.0f;
	//	//translation[2] = translation[2] / 1000.0f;


	//	cout <<rotation_matrix[0][0]<<" "<<rotation_matrix[0][1]<<" "<<rotation_matrix[0][2]<<" "<<translation[0]<<endl;
	//	cout <<rotation_matrix[1][0]<<" "<<rotation_matrix[1][1]<<" "<<rotation_matrix[1][2]<<" "<<translation[1]<<endl;
	//	cout <<rotation_matrix[2][0]<<" "<<rotation_matrix[2][1]<<" "<<rotation_matrix[2][2]<<" "<<translation[2]<<endl;

 // depth_pose.applyTransformAfter(translation, rotation_matrix);

 // //depth_pose.toLeftCamera(image.calibration()->depth_intrinsics,
 // //                          image.calibration()->R, image.calibration()->T);
 // //depth_pose1.toLeftCamera(image.calibration()->depth_intrinsics,
 // //                          image.calibration()->R, image.calibration()->T);


	//}
	//else
	//{
	//	cout<<" --optimizeWithICP false"<<endl;
	//}

	int i = 0;
	ofstream ofs("listplytemp.txt");
	ofs<<m_image_data.size() + 1<<endl;
	for (i = 0; i < m_image_data.size(); i++)
	{
		std::vector<Point3f> pts1;
		Pose3D depth_pose1 = m_image_data[i].depth_pose;
		rgbdImageToPointCloud(pts1, m_image_data[i].depth, depth_pose1);
		PointCloudToPlyFiles2(pts1, cv::format("temp%d.ply", i));

		ofs<<cv::format("temp%d.ply", i)<<endl;
	}

	std::vector<Point3f> pts2;
	rgbdImageToPointCloud(pts2, image.mappedDepth(), depth_pose);
	PointCloudToPlyFiles2(pts2, cv::format("temp%d.ply", i));

	ofs<<cv::format("temp%d.ply", i)<<endl;
	ofs.close();

	bool result = MyAlign::Auto("listplytemp.txt", "config");

	if (result)
	{
		//update all 
		cv::Vec3f translation;
		cv::Mat1d rotation_matrix(3, 3, 0.0f);
		for (i = 0; i < m_image_data.size(); i++)
		{
			getrtMatrixFromFile(cv::format("config\\temp%d.txt", i), translation, rotation_matrix);
			m_image_data[i].depth_pose.applyTransformAfter(translation, rotation_matrix);

			Pose3D new_rgb_pose = m_image_data[i].depth_pose;
			new_rgb_pose.toRightCamera(image.calibration()->rgb_intrinsics,
				image.calibration()->R, image.calibration()->T);
			m_features[i].compute3dLocation(new_rgb_pose);
		}

		getrtMatrixFromFile(cv::format("config\\temp%d.txt", i), translation, rotation_matrix);
		depth_pose.applyTransformAfter(translation, rotation_matrix);

	}
	else
	{
		cout<<" --optimizeWithICP false"<<endl;
	}

	return result;
}
} // ntk
