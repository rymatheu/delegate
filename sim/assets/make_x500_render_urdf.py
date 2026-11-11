"""Write sim/assets/x500_render.urdf: a visual-only model of the X500 for rendering recorded
flights, generated from the visuals of PX4's Gazebo model (PX4-gazebo-models, BSD 3-Clause,
models/x500_base/model.sdf; meshes copied to sim/assets/x500_meshes/). The base link carries the
frame and motor-base meshes; each rotor is its own link (propeller and motor bell) on a continuous
joint about body z at the rotor's position, named rotor_0..3 as in the SDF (rotor_0 front right,
rotor_1 rear left, both CCW; rotor_2 front left, rotor_3 rear right, both CW), so a renderer can
turn the propellers. A second file, x500_render_noprops.urdf, leaves the propeller meshes out. The three logo planes are left out. The physics model is sim/assets/x500.urdf.
Usage: make_x500_render_urdf.py path/to/x500_base/model.sdf
"""
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

here = Path(__file__).parent
root = ET.parse(sys.argv[1]).getroot()
pose = lambda s: [float(x) for x in (s or "0 0 0 0 0 0").split()]
color = {"NXP-HGD-CF.dae": "0.10 0.10 0.11 1", "5010Base.dae": "0.55 0.55 0.58 1", "5010Bell.dae": "0.20 0.20 0.22 1"}
inertial = '    <inertial><mass value="0.001"/><inertia ixx="1e-6" ixy="0" ixz="0" iyy="1e-6" iyz="0" izz="1e-6"/></inertial>'
def write(fname, with_props):
  out, joints, n = ['<?xml version="1.0"?>', '<robot name="x500_render">'], [], 0
  for link in root.iter("link"):
      name, lp = link.get("name"), pose(link.findtext("pose"))
      meshes = [v for v in link.findall("visual") if v.find("geometry/mesh") is not None
              and (with_props or not v.find("geometry/mesh").findtext("uri").endswith(".stl"))]
      if not meshes:
          continue
      out += [f'  <link name="{name}">', inertial]
      for v in meshes:
          mesh, vp = v.find("geometry/mesh"), pose(v.findtext("pose"))
          f = mesh.findtext("uri").split("/")[-1]
          rgba = color.get(f) or ("0.85 0.22 0.12 1" if lp[0] > 0 else "0.12 0.12 0.13 1")   # front propellers red
          out += ['    <visual>', f'      <origin xyz="{vp[0]} {vp[1]} {vp[2]}" rpy="{vp[3]} {vp[4]} {vp[5]}"/>',
                  f'      <geometry><mesh filename="x500_meshes/{f}" scale="{mesh.findtext("scale") or "1 1 1"}"/></geometry>',
                  f'      <material name="m{n}"><color rgba="{rgba}"/></material>', '    </visual>']
          n += 1
      out.append('  </link>')
      if name != "base_link":
          joints += [f'  <joint name="{name}_joint" type="continuous">', '    <parent link="base_link"/>', f'    <child link="{name}"/>',
                     f'    <origin xyz="{lp[0]} {lp[1]} {lp[2]}" rpy="{lp[3]} {lp[4]} {lp[5]}"/>', '    <axis xyz="0 0 1"/>', '  </joint>']
  (here / fname).write_text("\n".join(out + joints + ['</robot>']) + "\n")
  print(f"wrote {here / fname}: {n} mesh visuals, {len(joints) // 6} rotor joints")


write("x500_render.urdf", True)             # with the propeller meshes, for still views
write("x500_render_noprops.urdf", False)    # without them: the renderer draws the blades as motion blur
