"""Final isolated tests: block process creation and all socket operations."""
from pathlib import Path
import os
import runpy
import sys

root=Path(__file__).resolve().parent
blocked={'subprocess.Popen','os.system','os.posix_spawn','os.posix_spawnp',
         'socket.connect','socket.getaddrinfo','socket.__new__'}
def audit(event,args):
    if event in blocked:
        raise AssertionError('Isolated publication tests attempted forbidden external action: '+event)
    if event=='open':
        path,mode,flags=args
        if isinstance(path,(str,bytes,os.PathLike)) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND):
            if not Path(os.fsdecode(path)).resolve().is_relative_to(root):
                raise AssertionError('Test write escapes publication-prep')
    if event in {'os.mkdir','os.remove','os.rmdir'} and args and isinstance(args[0],(str,bytes,os.PathLike)):
        path=Path(os.fsdecode(args[0]))
        # shutil may use paths relative to an already-open directory descriptor.
        if path.is_absolute() and not path.resolve().is_relative_to(root):
            raise AssertionError('Test filesystem mutation escapes publication-prep')
sys.addaudithook(audit)
sys.argv=[str(root/'test_chapter8_publication.py')]
runpy.run_path(sys.argv[0],run_name='__main__')
