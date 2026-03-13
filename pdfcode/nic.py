import requests
import fitz  # PyMuPDF
import io
from urllib.parse import parse_qs

def split_url(url): 
    pdf_index = url.lower().find('.pdf')
    if pdf_index == -1:
        return url, ''
    part1 = url[:pdf_index + 4]  # Include ".pdf"
    part2 = url[pdf_index + 4:]  # Everything after ".pdf"
    return part1.strip(), part2.strip()

def extract_temp_id(query_string):
    params = parse_qs(query_string)
    return params.get("temp_id", [""])[0]

def redraw_black_rectangles_from_api(pdf_url, temp_id):
    """Download PDF, apply redactions from API, return redacted PDF bytes."""
    try:
        # Step 1: Download the PDF
        response = requests.get(pdf_url, timeout=10)
        if response.status_code != 200:
            print("Failed to download PDF:", response.text)
            return None

        pdf_data = io.BytesIO(response.content)
        doc = fitz.open(stream=pdf_data, filetype="pdf")

        # Step 2: Fetch redaction data using temp_id
        api_url = f"https://idms-dev.blockchaincloudapps.com/api/v1/get-pdf-viewer-redact-info?temp_id={temp_id}"
        headers = {'Content-Type': 'application/json'}
        redact_response = requests.get(api_url, headers=headers, timeout=10)

        if redact_response.status_code != 200:
            print("Failed to fetch redaction data:", redact_response.text)
            return None

        redact_data = redact_response.json()
        results = [(item["coordinate"], item["page_size"], item["zoom_size"]) for item in redact_data["data"]]

        # Step 3: Draw redaction rectangles
        for coord_str, saved_pagesize_str, _ in results:
            coord = eval(coord_str)
            saved_pagesize = eval(saved_pagesize_str)
            page_num = coord['page']

            page = doc.load_page(page_num)
            actual_width, actual_height = page.rect.width, page.rect.height

            scale_x = actual_width / saved_pagesize[0]
            scale_y = actual_height / saved_pagesize[1]

            x1 = coord['x1'] * scale_x
            y1 = coord['y1'] * scale_y
            x2 = coord['x2'] * scale_x
            y2 = coord['y2'] * scale_y

            rect = fitz.Rect(x1, y1, x2, y2)

            shape = page.new_shape()
            if coord.get('filled', True):
                shape.draw_rect(rect)
                shape.finish(fill=(0, 0, 0), color=None)
            else:
                shape.draw_rect(rect)
                shape.finish(color=(0, 0, 0), fill=None)

            shape.commit()

        # Step 4: Save modified PDF to memory
        redacted_pdf = io.BytesIO()
        doc.save(redacted_pdf)
        doc.close()
        redacted_pdf.seek(0)
        print("Redaction complete and saved.")
        return redacted_pdf  # You can return this to stream or save to disk

    except Exception as e:
        print(f"Error during redaction: {e}")
        return None




sample_url = "https://idms-backend.blockchaincloudapps.com/documents/1085671-MCLAUGHLIN, SHAUN/File-1085671-MCLAUGHLIN, SHAUN/New mail/07-02-2025_08-18-37-84-Return_Mail_redact_with_annotations.pdf?user_id=8d8976c6-0554-4bac-bd22-1d9659b0faae&view_redact=false&doc_id=828633e7-4ccc-47b1-86d9-4da715ce1b3a&display_name=Return Mail.pdf&date_time=07-02-2025 13:48:39&account_name=sanjay.vm&timer_id=b113c68d-995d-48c8-ac42-c53c7ca36edd&is_freeze=false&temp_id=3be09035-571a-11f0-8314-dc2148e3e617"

pdf_url, query_string = split_url(sample_url)
temp_id = extract_temp_id(query_string)

# Run redaction
redacted_file = redraw_black_rectangles_from_api(pdf_url, temp_id)

# Save to disk for verification
if redacted_file:
    with open("redacted_output.pdf", "wb") as f:
        f.write(redacted_file.read())













# from flask import Flask, request, send_file, Response
# import requests
# import fitz  # PyMuPDF
# import io
# from urllib.parse import parse_qs
# from uuid import uuid4

# app = Flask(__name__)

# def split_url(url):
#     pdf_index = url.lower().find('.pdf')
#     if pdf_index == -1:
#         return url, ''
#     part1 = url[:pdf_index + 4]  # Include ".pdf"
#     part2 = url[pdf_index + 4:]  # Everything after ".pdf"
#     return part1.strip(), part2.strip()

# def extract_temp_id(query_string):
#     params = parse_qs(query_string)
#     return params.get("temp_id", [""])[0]

# @app.route('/redact-pdf', methods=['GET'])
# def redact_pdf():
#     try:
#         pdf_url = request.args.get('pdf_url')
#         if not pdf_url:
#             return Response("Missing pdf_url parameter", status=400)

#         pdf_base_url, query_string = split_url(pdf_url)
#         temp_id = request.args.get('temp_id') or extract_temp_id(query_string)
#         if not temp_id:
#             return Response("Missing temp_id parameter", status=400)

#         response = requests.get(pdf_base_url, timeout=10)
#         if response.status_code != 200:
#             return Response(f"Failed to download PDF: {response.text}", status=response.status_code)

#         pdf_data = io.BytesIO(response.content)
#         doc = fitz.open(stream=pdf_data, filetype="pdf")

#         api_url = f"https://idms-dev.blockchaincloudapps.com/api/v1/get-pdf-viewer-redact-info?temp_id={temp_id}"
#         headers = {'Content-Type': 'application/json'}
#         redact_response = requests.get(api_url, headers=headers, timeout=10)

#         if redact_response.status_code != 200:
#             return Response(f"Failed to fetch redaction data: {redact_response.text}", status=redact_response.status_code)

#         redact_data = redact_response.json()
#         results = [(item["coordinate"], item["page_size"], item["zoom_size"]) for item in redact_data["data"]]

#         for coord_str, saved_pagesize_str, _ in results:
#             coord = eval(coord_str)
#             saved_pagesize = eval(saved_pagesize_str)
#             page_num = coord['page']

#             page = doc.load_page(page_num)
#             actual_width, actual_height = page.rect.width, page.rect.height

#             scale_x = actual_width / saved_pagesize[0]
#             scale_y = actual_height / saved_pagesize[1]

#             x1 = coord['x1'] * scale_x
#             y1 = coord['y1'] * scale_y
#             x2 = coord['x2'] * scale_x
#             y2 = coord['y2'] * scale_y

#             rect = fitz.Rect(x1, y1, x2, y2)

#             shape = page.new_shape()
#             if coord.get('filled', True):
#                 shape.draw_rect(rect)
#                 shape.finish(fill=(0, 0, 0), color=None)
#             else:
#                 shape.draw_rect(rect)
#                 shape.finish(color=(0, 0, 0), fill=None)

#             shape.commit()

#         redacted_pdf = io.BytesIO()
#         doc.save(redacted_pdf)
#         doc.close()
#         redacted_pdf.seek(0)

#         return send_file(
#             redacted_pdf,
#             mimetype='application/pdf',
#             as_attachment=True,
#             download_name=f'redacted_{uuid4()}.pdf'
#         )

#     except Exception as e:
#         return Response(f"Error during redaction: {str(e)}", status=500)

# if __name__ == '__main__':
#     app.run(debug=True)















