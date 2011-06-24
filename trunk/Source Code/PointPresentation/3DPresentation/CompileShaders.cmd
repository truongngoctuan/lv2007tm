for /f "tokens=*" %%a in ('dir /b *.vs.hlsl') do (
call "%%DXSDK_DIR%%Utilities\bin\x86\fxc.exe" /T vs_2_0 /O3 /Zpr /Fo %%~na %%a >> hlslcomplog.txt
)
for /f "tokens=*" %%a in ('dir /b *.ps.hlsl') do (
call "%%DXSDK_DIR%%Utilities\bin\x86\fxc.exe" /T ps_2_0 /O3 /Zpr /Fo %%~na %%a >> hlslcomplog.txt
)