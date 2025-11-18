import asyncio
import aristotlelib
import shutil

with open("Aristotle/apikey.txt", "r", encoding="utf-8") as file:
    api_key = file.read()

aristotlelib.set_api_key(api_key)

target_id = "Pauli.lean"
context = []

target_path = f'ATPTest/Unitary{target_id}'
solution_path = f'Aristotle/Solutions/{target_id}'

async def main():
    
    # Create a new project
    project = await aristotlelib.Project.create()
    print(f"Created project: {project.project_id}")

    # Manually add files needed for import
    await project.add_context(context)

    # Prove a theorem from a Lean file
    sp = await project.prove_from_file(target_path, auto_add_imports=True)
    shutil.move(sp, solution_path)
    #print(f"Solution saved to: {solution_path}")
    print(f"Solution saved to: {solution_path}")

asyncio.run(main())
