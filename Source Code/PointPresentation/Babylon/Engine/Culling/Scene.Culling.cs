using System.Collections.Generic;
using System.Linq;

namespace Babylon
{
    partial class Scene
    {
        readonly List<SubModel> standardSubModels = new List<SubModel>();
        readonly List<SubModel> opacitySubModels = new List<SubModel>();
        readonly List<SubModel> alphaSubModels = new List<SubModel>();
        readonly List<Model> activeModels = new List<Model>();

        void SelectVisibleWorld()
        {
            // Cameras
            ActiveCamera.ComputeMatrices();

            // Lights
            foreach (var light in Lights)
            {
                light.ComputeMatrices();
            }

            // Objects
            activeModels.Clear();
            standardSubModels.Clear();
            alphaSubModels.Clear();
            opacitySubModels.Clear();           

            foreach (Model model in models)
            {
                if (!model.Enabled)
                    continue;

                if (model.StreamingState != StreamingState.Loaded)
                {
                    if (model.StreamingState == StreamingState.PreLoaded)
                    {
                        RegisterForStreaming(model);
                    }
                    continue;
                }

                model.ComputeMatrices();

                if (!ActiveCamera.IsInFrustrum(model.BoundingInfo))
                    continue;

                activeModels.Add(model);

                if (!model.Renderable || model.Visibility <= 0)
                    continue;

                foreach (SubModel subModel in model.SubModels)
                {
                    if (subModel.Material == null)
                        return;

                    if (model.SubModels.Count > 1 && !ActiveCamera.IsInFrustrum(subModel.BoundingInfo))
                        continue;

                    subModel.DistanceToActiveCamera = (subModel.Parent.Position - ActiveCamera.Position).Length();

                    if (subModel.Material.IsOpacity)
                        opacitySubModels.Add(subModel);
                    else if (subModel.Alpha != 1.0f || subModel.Material.HasAlpha)
                        alphaSubModels.Add(subModel);
                    else
                        standardSubModels.Add(subModel);

                    RenderedVerticesCount += subModel.VerticesCount;
                    RenderedFacesCount += subModel.FacesCount;
                }
            }

            // Ordering alpha submodels
            alphaSubModels.Sort((a, b) =>
                                    {
                                        if (a.DistanceToActiveCamera == b.DistanceToActiveCamera)
                                            return 0;

                                        return a.DistanceToActiveCamera < b.DistanceToActiveCamera ? -1 : 1;
                                    }
                                    );
        }
    }
}
